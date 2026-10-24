import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay007
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_007 (j : Fin 64) (hj : 64*7+j.val < 2540) :
    DPay (64*7+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_448
  · exact WuPaper.ClassicalFourthNat.DPay_449
  · exact WuPaper.ClassicalFourthNat.DPay_450
  · exact WuPaper.ClassicalFourthNat.DPay_451
  · exact WuPaper.ClassicalFourthNat.DPay_452
  · exact WuPaper.ClassicalFourthNat.DPay_453
  · exact WuPaper.ClassicalFourthNat.DPay_454
  · exact WuPaper.ClassicalFourthNat.DPay_455
  · exact WuPaper.ClassicalFourthNat.DPay_456
  · exact WuPaper.ClassicalFourthNat.DPay_457
  · exact WuPaper.ClassicalFourthNat.DPay_458
  · exact WuPaper.ClassicalFourthNat.DPay_459
  · exact WuPaper.ClassicalFourthNat.DPay_460
  · exact WuPaper.ClassicalFourthNat.DPay_461
  · exact WuPaper.ClassicalFourthNat.DPay_462
  · exact WuPaper.ClassicalFourthNat.DPay_463
  · exact WuPaper.ClassicalFourthNat.DPay_464
  · exact WuPaper.ClassicalFourthNat.DPay_465
  · exact WuPaper.ClassicalFourthNat.DPay_466
  · exact WuPaper.ClassicalFourthNat.DPay_467
  · exact WuPaper.ClassicalFourthNat.DPay_468
  · exact WuPaper.ClassicalFourthNat.DPay_469
  · exact WuPaper.ClassicalFourthNat.DPay_470
  · exact WuPaper.ClassicalFourthNat.DPay_471
  · exact WuPaper.ClassicalFourthNat.DPay_472
  · exact WuPaper.ClassicalFourthNat.DPay_473
  · exact WuPaper.ClassicalFourthNat.DPay_474
  · exact WuPaper.ClassicalFourthNat.DPay_475
  · exact WuPaper.ClassicalFourthNat.DPay_476
  · exact WuPaper.ClassicalFourthNat.DPay_477
  · exact WuPaper.ClassicalFourthNat.DPay_478
  · exact WuPaper.ClassicalFourthNat.DPay_479
  · exact WuPaper.ClassicalFourthNat.DPay_480
  · exact WuPaper.ClassicalFourthNat.DPay_481
  · exact WuPaper.ClassicalFourthNat.DPay_482
  · exact WuPaper.ClassicalFourthNat.DPay_483
  · exact WuPaper.ClassicalFourthNat.DPay_484
  · exact WuPaper.ClassicalFourthNat.DPay_485
  · exact WuPaper.ClassicalFourthNat.DPay_486
  · exact WuPaper.ClassicalFourthNat.DPay_487
  · exact WuPaper.ClassicalFourthNat.DPay_488
  · exact WuPaper.ClassicalFourthNat.DPay_489
  · exact WuPaper.ClassicalFourthNat.DPay_490
  · exact WuPaper.ClassicalFourthNat.DPay_491
  · exact WuPaper.ClassicalFourthNat.DPay_492
  · exact WuPaper.ClassicalFourthNat.DPay_493
  · exact WuPaper.ClassicalFourthNat.DPay_494
  · exact WuPaper.ClassicalFourthNat.DPay_495
  · exact WuPaper.ClassicalFourthNat.DPay_496
  · exact WuPaper.ClassicalFourthNat.DPay_497
  · exact WuPaper.ClassicalFourthNat.DPay_498
  · exact WuPaper.ClassicalFourthNat.DPay_499
  · exact WuPaper.ClassicalFourthNat.DPay_500
  · exact WuPaper.ClassicalFourthNat.DPay_501
  · exact WuPaper.ClassicalFourthNat.DPay_502
  · exact WuPaper.ClassicalFourthNat.DPay_503
  · exact WuPaper.ClassicalFourthNat.DPay_504
  · exact WuPaper.ClassicalFourthNat.DPay_505
  · exact WuPaper.ClassicalFourthNat.DPay_506
  · exact WuPaper.ClassicalFourthNat.DPay_507
  · exact WuPaper.ClassicalFourthNat.DPay_508
  · exact WuPaper.ClassicalFourthNat.DPay_509
  · exact WuPaper.ClassicalFourthNat.DPay_510
  · exact WuPaper.ClassicalFourthNat.DPay_511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_007

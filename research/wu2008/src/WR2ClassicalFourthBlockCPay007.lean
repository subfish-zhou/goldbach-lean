import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay007
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_007 (j : Fin 64) (hj : 64*7+j.val < 2540) :
    CPay (64*7+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_448
  · exact WuPaper.ClassicalFourthNat.CPay_449
  · exact WuPaper.ClassicalFourthNat.CPay_450
  · exact WuPaper.ClassicalFourthNat.CPay_451
  · exact WuPaper.ClassicalFourthNat.CPay_452
  · exact WuPaper.ClassicalFourthNat.CPay_453
  · exact WuPaper.ClassicalFourthNat.CPay_454
  · exact WuPaper.ClassicalFourthNat.CPay_455
  · exact WuPaper.ClassicalFourthNat.CPay_456
  · exact WuPaper.ClassicalFourthNat.CPay_457
  · exact WuPaper.ClassicalFourthNat.CPay_458
  · exact WuPaper.ClassicalFourthNat.CPay_459
  · exact WuPaper.ClassicalFourthNat.CPay_460
  · exact WuPaper.ClassicalFourthNat.CPay_461
  · exact WuPaper.ClassicalFourthNat.CPay_462
  · exact WuPaper.ClassicalFourthNat.CPay_463
  · exact WuPaper.ClassicalFourthNat.CPay_464
  · exact WuPaper.ClassicalFourthNat.CPay_465
  · exact WuPaper.ClassicalFourthNat.CPay_466
  · exact WuPaper.ClassicalFourthNat.CPay_467
  · exact WuPaper.ClassicalFourthNat.CPay_468
  · exact WuPaper.ClassicalFourthNat.CPay_469
  · exact WuPaper.ClassicalFourthNat.CPay_470
  · exact WuPaper.ClassicalFourthNat.CPay_471
  · exact WuPaper.ClassicalFourthNat.CPay_472
  · exact WuPaper.ClassicalFourthNat.CPay_473
  · exact WuPaper.ClassicalFourthNat.CPay_474
  · exact WuPaper.ClassicalFourthNat.CPay_475
  · exact WuPaper.ClassicalFourthNat.CPay_476
  · exact WuPaper.ClassicalFourthNat.CPay_477
  · exact WuPaper.ClassicalFourthNat.CPay_478
  · exact WuPaper.ClassicalFourthNat.CPay_479
  · exact WuPaper.ClassicalFourthNat.CPay_480
  · exact WuPaper.ClassicalFourthNat.CPay_481
  · exact WuPaper.ClassicalFourthNat.CPay_482
  · exact WuPaper.ClassicalFourthNat.CPay_483
  · exact WuPaper.ClassicalFourthNat.CPay_484
  · exact WuPaper.ClassicalFourthNat.CPay_485
  · exact WuPaper.ClassicalFourthNat.CPay_486
  · exact WuPaper.ClassicalFourthNat.CPay_487
  · exact WuPaper.ClassicalFourthNat.CPay_488
  · exact WuPaper.ClassicalFourthNat.CPay_489
  · exact WuPaper.ClassicalFourthNat.CPay_490
  · exact WuPaper.ClassicalFourthNat.CPay_491
  · exact WuPaper.ClassicalFourthNat.CPay_492
  · exact WuPaper.ClassicalFourthNat.CPay_493
  · exact WuPaper.ClassicalFourthNat.CPay_494
  · exact WuPaper.ClassicalFourthNat.CPay_495
  · exact WuPaper.ClassicalFourthNat.CPay_496
  · exact WuPaper.ClassicalFourthNat.CPay_497
  · exact WuPaper.ClassicalFourthNat.CPay_498
  · exact WuPaper.ClassicalFourthNat.CPay_499
  · exact WuPaper.ClassicalFourthNat.CPay_500
  · exact WuPaper.ClassicalFourthNat.CPay_501
  · exact WuPaper.ClassicalFourthNat.CPay_502
  · exact WuPaper.ClassicalFourthNat.CPay_503
  · exact WuPaper.ClassicalFourthNat.CPay_504
  · exact WuPaper.ClassicalFourthNat.CPay_505
  · exact WuPaper.ClassicalFourthNat.CPay_506
  · exact WuPaper.ClassicalFourthNat.CPay_507
  · exact WuPaper.ClassicalFourthNat.CPay_508
  · exact WuPaper.ClassicalFourthNat.CPay_509
  · exact WuPaper.ClassicalFourthNat.CPay_510
  · exact WuPaper.ClassicalFourthNat.CPay_511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_007

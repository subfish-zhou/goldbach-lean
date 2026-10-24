import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint007
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_007 (j : Fin 64) (hj : 64*7+j.val < 10541) :
    OuterPoint (64*7+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_448
  · exact WuPaper.ClassicalFourthNat.OuterPoint_449
  · exact WuPaper.ClassicalFourthNat.OuterPoint_450
  · exact WuPaper.ClassicalFourthNat.OuterPoint_451
  · exact WuPaper.ClassicalFourthNat.OuterPoint_452
  · exact WuPaper.ClassicalFourthNat.OuterPoint_453
  · exact WuPaper.ClassicalFourthNat.OuterPoint_454
  · exact WuPaper.ClassicalFourthNat.OuterPoint_455
  · exact WuPaper.ClassicalFourthNat.OuterPoint_456
  · exact WuPaper.ClassicalFourthNat.OuterPoint_457
  · exact WuPaper.ClassicalFourthNat.OuterPoint_458
  · exact WuPaper.ClassicalFourthNat.OuterPoint_459
  · exact WuPaper.ClassicalFourthNat.OuterPoint_460
  · exact WuPaper.ClassicalFourthNat.OuterPoint_461
  · exact WuPaper.ClassicalFourthNat.OuterPoint_462
  · exact WuPaper.ClassicalFourthNat.OuterPoint_463
  · exact WuPaper.ClassicalFourthNat.OuterPoint_464
  · exact WuPaper.ClassicalFourthNat.OuterPoint_465
  · exact WuPaper.ClassicalFourthNat.OuterPoint_466
  · exact WuPaper.ClassicalFourthNat.OuterPoint_467
  · exact WuPaper.ClassicalFourthNat.OuterPoint_468
  · exact WuPaper.ClassicalFourthNat.OuterPoint_469
  · exact WuPaper.ClassicalFourthNat.OuterPoint_470
  · exact WuPaper.ClassicalFourthNat.OuterPoint_471
  · exact WuPaper.ClassicalFourthNat.OuterPoint_472
  · exact WuPaper.ClassicalFourthNat.OuterPoint_473
  · exact WuPaper.ClassicalFourthNat.OuterPoint_474
  · exact WuPaper.ClassicalFourthNat.OuterPoint_475
  · exact WuPaper.ClassicalFourthNat.OuterPoint_476
  · exact WuPaper.ClassicalFourthNat.OuterPoint_477
  · exact WuPaper.ClassicalFourthNat.OuterPoint_478
  · exact WuPaper.ClassicalFourthNat.OuterPoint_479
  · exact WuPaper.ClassicalFourthNat.OuterPoint_480
  · exact WuPaper.ClassicalFourthNat.OuterPoint_481
  · exact WuPaper.ClassicalFourthNat.OuterPoint_482
  · exact WuPaper.ClassicalFourthNat.OuterPoint_483
  · exact WuPaper.ClassicalFourthNat.OuterPoint_484
  · exact WuPaper.ClassicalFourthNat.OuterPoint_485
  · exact WuPaper.ClassicalFourthNat.OuterPoint_486
  · exact WuPaper.ClassicalFourthNat.OuterPoint_487
  · exact WuPaper.ClassicalFourthNat.OuterPoint_488
  · exact WuPaper.ClassicalFourthNat.OuterPoint_489
  · exact WuPaper.ClassicalFourthNat.OuterPoint_490
  · exact WuPaper.ClassicalFourthNat.OuterPoint_491
  · exact WuPaper.ClassicalFourthNat.OuterPoint_492
  · exact WuPaper.ClassicalFourthNat.OuterPoint_493
  · exact WuPaper.ClassicalFourthNat.OuterPoint_494
  · exact WuPaper.ClassicalFourthNat.OuterPoint_495
  · exact WuPaper.ClassicalFourthNat.OuterPoint_496
  · exact WuPaper.ClassicalFourthNat.OuterPoint_497
  · exact WuPaper.ClassicalFourthNat.OuterPoint_498
  · exact WuPaper.ClassicalFourthNat.OuterPoint_499
  · exact WuPaper.ClassicalFourthNat.OuterPoint_500
  · exact WuPaper.ClassicalFourthNat.OuterPoint_501
  · exact WuPaper.ClassicalFourthNat.OuterPoint_502
  · exact WuPaper.ClassicalFourthNat.OuterPoint_503
  · exact WuPaper.ClassicalFourthNat.OuterPoint_504
  · exact WuPaper.ClassicalFourthNat.OuterPoint_505
  · exact WuPaper.ClassicalFourthNat.OuterPoint_506
  · exact WuPaper.ClassicalFourthNat.OuterPoint_507
  · exact WuPaper.ClassicalFourthNat.OuterPoint_508
  · exact WuPaper.ClassicalFourthNat.OuterPoint_509
  · exact WuPaper.ClassicalFourthNat.OuterPoint_510
  · exact WuPaper.ClassicalFourthNat.OuterPoint_511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_007

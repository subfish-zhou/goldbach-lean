import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint008
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_008 (j : Fin 64) (hj : 64*8+j.val < 10541) :
    OuterPoint (64*8+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_512
  · exact WuPaper.ClassicalFourthNat.OuterPoint_513
  · exact WuPaper.ClassicalFourthNat.OuterPoint_514
  · exact WuPaper.ClassicalFourthNat.OuterPoint_515
  · exact WuPaper.ClassicalFourthNat.OuterPoint_516
  · exact WuPaper.ClassicalFourthNat.OuterPoint_517
  · exact WuPaper.ClassicalFourthNat.OuterPoint_518
  · exact WuPaper.ClassicalFourthNat.OuterPoint_519
  · exact WuPaper.ClassicalFourthNat.OuterPoint_520
  · exact WuPaper.ClassicalFourthNat.OuterPoint_521
  · exact WuPaper.ClassicalFourthNat.OuterPoint_522
  · exact WuPaper.ClassicalFourthNat.OuterPoint_523
  · exact WuPaper.ClassicalFourthNat.OuterPoint_524
  · exact WuPaper.ClassicalFourthNat.OuterPoint_525
  · exact WuPaper.ClassicalFourthNat.OuterPoint_526
  · exact WuPaper.ClassicalFourthNat.OuterPoint_527
  · exact WuPaper.ClassicalFourthNat.OuterPoint_528
  · exact WuPaper.ClassicalFourthNat.OuterPoint_529
  · exact WuPaper.ClassicalFourthNat.OuterPoint_530
  · exact WuPaper.ClassicalFourthNat.OuterPoint_531
  · exact WuPaper.ClassicalFourthNat.OuterPoint_532
  · exact WuPaper.ClassicalFourthNat.OuterPoint_533
  · exact WuPaper.ClassicalFourthNat.OuterPoint_534
  · exact WuPaper.ClassicalFourthNat.OuterPoint_535
  · exact WuPaper.ClassicalFourthNat.OuterPoint_536
  · exact WuPaper.ClassicalFourthNat.OuterPoint_537
  · exact WuPaper.ClassicalFourthNat.OuterPoint_538
  · exact WuPaper.ClassicalFourthNat.OuterPoint_539
  · exact WuPaper.ClassicalFourthNat.OuterPoint_540
  · exact WuPaper.ClassicalFourthNat.OuterPoint_541
  · exact WuPaper.ClassicalFourthNat.OuterPoint_542
  · exact WuPaper.ClassicalFourthNat.OuterPoint_543
  · exact WuPaper.ClassicalFourthNat.OuterPoint_544
  · exact WuPaper.ClassicalFourthNat.OuterPoint_545
  · exact WuPaper.ClassicalFourthNat.OuterPoint_546
  · exact WuPaper.ClassicalFourthNat.OuterPoint_547
  · exact WuPaper.ClassicalFourthNat.OuterPoint_548
  · exact WuPaper.ClassicalFourthNat.OuterPoint_549
  · exact WuPaper.ClassicalFourthNat.OuterPoint_550
  · exact WuPaper.ClassicalFourthNat.OuterPoint_551
  · exact WuPaper.ClassicalFourthNat.OuterPoint_552
  · exact WuPaper.ClassicalFourthNat.OuterPoint_553
  · exact WuPaper.ClassicalFourthNat.OuterPoint_554
  · exact WuPaper.ClassicalFourthNat.OuterPoint_555
  · exact WuPaper.ClassicalFourthNat.OuterPoint_556
  · exact WuPaper.ClassicalFourthNat.OuterPoint_557
  · exact WuPaper.ClassicalFourthNat.OuterPoint_558
  · exact WuPaper.ClassicalFourthNat.OuterPoint_559
  · exact WuPaper.ClassicalFourthNat.OuterPoint_560
  · exact WuPaper.ClassicalFourthNat.OuterPoint_561
  · exact WuPaper.ClassicalFourthNat.OuterPoint_562
  · exact WuPaper.ClassicalFourthNat.OuterPoint_563
  · exact WuPaper.ClassicalFourthNat.OuterPoint_564
  · exact WuPaper.ClassicalFourthNat.OuterPoint_565
  · exact WuPaper.ClassicalFourthNat.OuterPoint_566
  · exact WuPaper.ClassicalFourthNat.OuterPoint_567
  · exact WuPaper.ClassicalFourthNat.OuterPoint_568
  · exact WuPaper.ClassicalFourthNat.OuterPoint_569
  · exact WuPaper.ClassicalFourthNat.OuterPoint_570
  · exact WuPaper.ClassicalFourthNat.OuterPoint_571
  · exact WuPaper.ClassicalFourthNat.OuterPoint_572
  · exact WuPaper.ClassicalFourthNat.OuterPoint_573
  · exact WuPaper.ClassicalFourthNat.OuterPoint_574
  · exact WuPaper.ClassicalFourthNat.OuterPoint_575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_008

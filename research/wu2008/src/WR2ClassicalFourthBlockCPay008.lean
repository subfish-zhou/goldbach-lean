import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay008
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_008 (j : Fin 64) (hj : 64*8+j.val < 2540) :
    CPay (64*8+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_512
  · exact WuPaper.ClassicalFourthNat.CPay_513
  · exact WuPaper.ClassicalFourthNat.CPay_514
  · exact WuPaper.ClassicalFourthNat.CPay_515
  · exact WuPaper.ClassicalFourthNat.CPay_516
  · exact WuPaper.ClassicalFourthNat.CPay_517
  · exact WuPaper.ClassicalFourthNat.CPay_518
  · exact WuPaper.ClassicalFourthNat.CPay_519
  · exact WuPaper.ClassicalFourthNat.CPay_520
  · exact WuPaper.ClassicalFourthNat.CPay_521
  · exact WuPaper.ClassicalFourthNat.CPay_522
  · exact WuPaper.ClassicalFourthNat.CPay_523
  · exact WuPaper.ClassicalFourthNat.CPay_524
  · exact WuPaper.ClassicalFourthNat.CPay_525
  · exact WuPaper.ClassicalFourthNat.CPay_526
  · exact WuPaper.ClassicalFourthNat.CPay_527
  · exact WuPaper.ClassicalFourthNat.CPay_528
  · exact WuPaper.ClassicalFourthNat.CPay_529
  · exact WuPaper.ClassicalFourthNat.CPay_530
  · exact WuPaper.ClassicalFourthNat.CPay_531
  · exact WuPaper.ClassicalFourthNat.CPay_532
  · exact WuPaper.ClassicalFourthNat.CPay_533
  · exact WuPaper.ClassicalFourthNat.CPay_534
  · exact WuPaper.ClassicalFourthNat.CPay_535
  · exact WuPaper.ClassicalFourthNat.CPay_536
  · exact WuPaper.ClassicalFourthNat.CPay_537
  · exact WuPaper.ClassicalFourthNat.CPay_538
  · exact WuPaper.ClassicalFourthNat.CPay_539
  · exact WuPaper.ClassicalFourthNat.CPay_540
  · exact WuPaper.ClassicalFourthNat.CPay_541
  · exact WuPaper.ClassicalFourthNat.CPay_542
  · exact WuPaper.ClassicalFourthNat.CPay_543
  · exact WuPaper.ClassicalFourthNat.CPay_544
  · exact WuPaper.ClassicalFourthNat.CPay_545
  · exact WuPaper.ClassicalFourthNat.CPay_546
  · exact WuPaper.ClassicalFourthNat.CPay_547
  · exact WuPaper.ClassicalFourthNat.CPay_548
  · exact WuPaper.ClassicalFourthNat.CPay_549
  · exact WuPaper.ClassicalFourthNat.CPay_550
  · exact WuPaper.ClassicalFourthNat.CPay_551
  · exact WuPaper.ClassicalFourthNat.CPay_552
  · exact WuPaper.ClassicalFourthNat.CPay_553
  · exact WuPaper.ClassicalFourthNat.CPay_554
  · exact WuPaper.ClassicalFourthNat.CPay_555
  · exact WuPaper.ClassicalFourthNat.CPay_556
  · exact WuPaper.ClassicalFourthNat.CPay_557
  · exact WuPaper.ClassicalFourthNat.CPay_558
  · exact WuPaper.ClassicalFourthNat.CPay_559
  · exact WuPaper.ClassicalFourthNat.CPay_560
  · exact WuPaper.ClassicalFourthNat.CPay_561
  · exact WuPaper.ClassicalFourthNat.CPay_562
  · exact WuPaper.ClassicalFourthNat.CPay_563
  · exact WuPaper.ClassicalFourthNat.CPay_564
  · exact WuPaper.ClassicalFourthNat.CPay_565
  · exact WuPaper.ClassicalFourthNat.CPay_566
  · exact WuPaper.ClassicalFourthNat.CPay_567
  · exact WuPaper.ClassicalFourthNat.CPay_568
  · exact WuPaper.ClassicalFourthNat.CPay_569
  · exact WuPaper.ClassicalFourthNat.CPay_570
  · exact WuPaper.ClassicalFourthNat.CPay_571
  · exact WuPaper.ClassicalFourthNat.CPay_572
  · exact WuPaper.ClassicalFourthNat.CPay_573
  · exact WuPaper.ClassicalFourthNat.CPay_574
  · exact WuPaper.ClassicalFourthNat.CPay_575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_008

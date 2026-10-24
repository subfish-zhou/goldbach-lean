import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay008
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_008 (j : Fin 64) (hj : 64*8+j.val < 10540) :
    OuterPay (64*8+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_512
  · exact WuPaper.ClassicalFourthNat.outerPay_513
  · exact WuPaper.ClassicalFourthNat.outerPay_514
  · exact WuPaper.ClassicalFourthNat.outerPay_515
  · exact WuPaper.ClassicalFourthNat.outerPay_516
  · exact WuPaper.ClassicalFourthNat.outerPay_517
  · exact WuPaper.ClassicalFourthNat.outerPay_518
  · exact WuPaper.ClassicalFourthNat.outerPay_519
  · exact WuPaper.ClassicalFourthNat.outerPay_520
  · exact WuPaper.ClassicalFourthNat.outerPay_521
  · exact WuPaper.ClassicalFourthNat.outerPay_522
  · exact WuPaper.ClassicalFourthNat.outerPay_523
  · exact WuPaper.ClassicalFourthNat.outerPay_524
  · exact WuPaper.ClassicalFourthNat.outerPay_525
  · exact WuPaper.ClassicalFourthNat.outerPay_526
  · exact WuPaper.ClassicalFourthNat.outerPay_527
  · exact WuPaper.ClassicalFourthNat.outerPay_528
  · exact WuPaper.ClassicalFourthNat.outerPay_529
  · exact WuPaper.ClassicalFourthNat.outerPay_530
  · exact WuPaper.ClassicalFourthNat.outerPay_531
  · exact WuPaper.ClassicalFourthNat.outerPay_532
  · exact WuPaper.ClassicalFourthNat.outerPay_533
  · exact WuPaper.ClassicalFourthNat.outerPay_534
  · exact WuPaper.ClassicalFourthNat.outerPay_535
  · exact WuPaper.ClassicalFourthNat.outerPay_536
  · exact WuPaper.ClassicalFourthNat.outerPay_537
  · exact WuPaper.ClassicalFourthNat.outerPay_538
  · exact WuPaper.ClassicalFourthNat.outerPay_539
  · exact WuPaper.ClassicalFourthNat.outerPay_540
  · exact WuPaper.ClassicalFourthNat.outerPay_541
  · exact WuPaper.ClassicalFourthNat.outerPay_542
  · exact WuPaper.ClassicalFourthNat.outerPay_543
  · exact WuPaper.ClassicalFourthNat.outerPay_544
  · exact WuPaper.ClassicalFourthNat.outerPay_545
  · exact WuPaper.ClassicalFourthNat.outerPay_546
  · exact WuPaper.ClassicalFourthNat.outerPay_547
  · exact WuPaper.ClassicalFourthNat.outerPay_548
  · exact WuPaper.ClassicalFourthNat.outerPay_549
  · exact WuPaper.ClassicalFourthNat.outerPay_550
  · exact WuPaper.ClassicalFourthNat.outerPay_551
  · exact WuPaper.ClassicalFourthNat.outerPay_552
  · exact WuPaper.ClassicalFourthNat.outerPay_553
  · exact WuPaper.ClassicalFourthNat.outerPay_554
  · exact WuPaper.ClassicalFourthNat.outerPay_555
  · exact WuPaper.ClassicalFourthNat.outerPay_556
  · exact WuPaper.ClassicalFourthNat.outerPay_557
  · exact WuPaper.ClassicalFourthNat.outerPay_558
  · exact WuPaper.ClassicalFourthNat.outerPay_559
  · exact WuPaper.ClassicalFourthNat.outerPay_560
  · exact WuPaper.ClassicalFourthNat.outerPay_561
  · exact WuPaper.ClassicalFourthNat.outerPay_562
  · exact WuPaper.ClassicalFourthNat.outerPay_563
  · exact WuPaper.ClassicalFourthNat.outerPay_564
  · exact WuPaper.ClassicalFourthNat.outerPay_565
  · exact WuPaper.ClassicalFourthNat.outerPay_566
  · exact WuPaper.ClassicalFourthNat.outerPay_567
  · exact WuPaper.ClassicalFourthNat.outerPay_568
  · exact WuPaper.ClassicalFourthNat.outerPay_569
  · exact WuPaper.ClassicalFourthNat.outerPay_570
  · exact WuPaper.ClassicalFourthNat.outerPay_571
  · exact WuPaper.ClassicalFourthNat.outerPay_572
  · exact WuPaper.ClassicalFourthNat.outerPay_573
  · exact WuPaper.ClassicalFourthNat.outerPay_574
  · exact WuPaper.ClassicalFourthNat.outerPay_575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_008

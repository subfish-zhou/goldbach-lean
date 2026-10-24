import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay008
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_008 (j : Fin 64) (hj : 64*8+j.val < 2540) :
    DPay (64*8+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_512
  · exact WuPaper.ClassicalFourthNat.DPay_513
  · exact WuPaper.ClassicalFourthNat.DPay_514
  · exact WuPaper.ClassicalFourthNat.DPay_515
  · exact WuPaper.ClassicalFourthNat.DPay_516
  · exact WuPaper.ClassicalFourthNat.DPay_517
  · exact WuPaper.ClassicalFourthNat.DPay_518
  · exact WuPaper.ClassicalFourthNat.DPay_519
  · exact WuPaper.ClassicalFourthNat.DPay_520
  · exact WuPaper.ClassicalFourthNat.DPay_521
  · exact WuPaper.ClassicalFourthNat.DPay_522
  · exact WuPaper.ClassicalFourthNat.DPay_523
  · exact WuPaper.ClassicalFourthNat.DPay_524
  · exact WuPaper.ClassicalFourthNat.DPay_525
  · exact WuPaper.ClassicalFourthNat.DPay_526
  · exact WuPaper.ClassicalFourthNat.DPay_527
  · exact WuPaper.ClassicalFourthNat.DPay_528
  · exact WuPaper.ClassicalFourthNat.DPay_529
  · exact WuPaper.ClassicalFourthNat.DPay_530
  · exact WuPaper.ClassicalFourthNat.DPay_531
  · exact WuPaper.ClassicalFourthNat.DPay_532
  · exact WuPaper.ClassicalFourthNat.DPay_533
  · exact WuPaper.ClassicalFourthNat.DPay_534
  · exact WuPaper.ClassicalFourthNat.DPay_535
  · exact WuPaper.ClassicalFourthNat.DPay_536
  · exact WuPaper.ClassicalFourthNat.DPay_537
  · exact WuPaper.ClassicalFourthNat.DPay_538
  · exact WuPaper.ClassicalFourthNat.DPay_539
  · exact WuPaper.ClassicalFourthNat.DPay_540
  · exact WuPaper.ClassicalFourthNat.DPay_541
  · exact WuPaper.ClassicalFourthNat.DPay_542
  · exact WuPaper.ClassicalFourthNat.DPay_543
  · exact WuPaper.ClassicalFourthNat.DPay_544
  · exact WuPaper.ClassicalFourthNat.DPay_545
  · exact WuPaper.ClassicalFourthNat.DPay_546
  · exact WuPaper.ClassicalFourthNat.DPay_547
  · exact WuPaper.ClassicalFourthNat.DPay_548
  · exact WuPaper.ClassicalFourthNat.DPay_549
  · exact WuPaper.ClassicalFourthNat.DPay_550
  · exact WuPaper.ClassicalFourthNat.DPay_551
  · exact WuPaper.ClassicalFourthNat.DPay_552
  · exact WuPaper.ClassicalFourthNat.DPay_553
  · exact WuPaper.ClassicalFourthNat.DPay_554
  · exact WuPaper.ClassicalFourthNat.DPay_555
  · exact WuPaper.ClassicalFourthNat.DPay_556
  · exact WuPaper.ClassicalFourthNat.DPay_557
  · exact WuPaper.ClassicalFourthNat.DPay_558
  · exact WuPaper.ClassicalFourthNat.DPay_559
  · exact WuPaper.ClassicalFourthNat.DPay_560
  · exact WuPaper.ClassicalFourthNat.DPay_561
  · exact WuPaper.ClassicalFourthNat.DPay_562
  · exact WuPaper.ClassicalFourthNat.DPay_563
  · exact WuPaper.ClassicalFourthNat.DPay_564
  · exact WuPaper.ClassicalFourthNat.DPay_565
  · exact WuPaper.ClassicalFourthNat.DPay_566
  · exact WuPaper.ClassicalFourthNat.DPay_567
  · exact WuPaper.ClassicalFourthNat.DPay_568
  · exact WuPaper.ClassicalFourthNat.DPay_569
  · exact WuPaper.ClassicalFourthNat.DPay_570
  · exact WuPaper.ClassicalFourthNat.DPay_571
  · exact WuPaper.ClassicalFourthNat.DPay_572
  · exact WuPaper.ClassicalFourthNat.DPay_573
  · exact WuPaper.ClassicalFourthNat.DPay_574
  · exact WuPaper.ClassicalFourthNat.DPay_575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_008

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay008
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_008 (j : Fin 64) (hj : 64*8+j.val < 10540) :
    BPay (64*8+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_512
  · exact WuPaper.ClassicalFourthNat.BPay_513
  · exact WuPaper.ClassicalFourthNat.BPay_514
  · exact WuPaper.ClassicalFourthNat.BPay_515
  · exact WuPaper.ClassicalFourthNat.BPay_516
  · exact WuPaper.ClassicalFourthNat.BPay_517
  · exact WuPaper.ClassicalFourthNat.BPay_518
  · exact WuPaper.ClassicalFourthNat.BPay_519
  · exact WuPaper.ClassicalFourthNat.BPay_520
  · exact WuPaper.ClassicalFourthNat.BPay_521
  · exact WuPaper.ClassicalFourthNat.BPay_522
  · exact WuPaper.ClassicalFourthNat.BPay_523
  · exact WuPaper.ClassicalFourthNat.BPay_524
  · exact WuPaper.ClassicalFourthNat.BPay_525
  · exact WuPaper.ClassicalFourthNat.BPay_526
  · exact WuPaper.ClassicalFourthNat.BPay_527
  · exact WuPaper.ClassicalFourthNat.BPay_528
  · exact WuPaper.ClassicalFourthNat.BPay_529
  · exact WuPaper.ClassicalFourthNat.BPay_530
  · exact WuPaper.ClassicalFourthNat.BPay_531
  · exact WuPaper.ClassicalFourthNat.BPay_532
  · exact WuPaper.ClassicalFourthNat.BPay_533
  · exact WuPaper.ClassicalFourthNat.BPay_534
  · exact WuPaper.ClassicalFourthNat.BPay_535
  · exact WuPaper.ClassicalFourthNat.BPay_536
  · exact WuPaper.ClassicalFourthNat.BPay_537
  · exact WuPaper.ClassicalFourthNat.BPay_538
  · exact WuPaper.ClassicalFourthNat.BPay_539
  · exact WuPaper.ClassicalFourthNat.BPay_540
  · exact WuPaper.ClassicalFourthNat.BPay_541
  · exact WuPaper.ClassicalFourthNat.BPay_542
  · exact WuPaper.ClassicalFourthNat.BPay_543
  · exact WuPaper.ClassicalFourthNat.BPay_544
  · exact WuPaper.ClassicalFourthNat.BPay_545
  · exact WuPaper.ClassicalFourthNat.BPay_546
  · exact WuPaper.ClassicalFourthNat.BPay_547
  · exact WuPaper.ClassicalFourthNat.BPay_548
  · exact WuPaper.ClassicalFourthNat.BPay_549
  · exact WuPaper.ClassicalFourthNat.BPay_550
  · exact WuPaper.ClassicalFourthNat.BPay_551
  · exact WuPaper.ClassicalFourthNat.BPay_552
  · exact WuPaper.ClassicalFourthNat.BPay_553
  · exact WuPaper.ClassicalFourthNat.BPay_554
  · exact WuPaper.ClassicalFourthNat.BPay_555
  · exact WuPaper.ClassicalFourthNat.BPay_556
  · exact WuPaper.ClassicalFourthNat.BPay_557
  · exact WuPaper.ClassicalFourthNat.BPay_558
  · exact WuPaper.ClassicalFourthNat.BPay_559
  · exact WuPaper.ClassicalFourthNat.BPay_560
  · exact WuPaper.ClassicalFourthNat.BPay_561
  · exact WuPaper.ClassicalFourthNat.BPay_562
  · exact WuPaper.ClassicalFourthNat.BPay_563
  · exact WuPaper.ClassicalFourthNat.BPay_564
  · exact WuPaper.ClassicalFourthNat.BPay_565
  · exact WuPaper.ClassicalFourthNat.BPay_566
  · exact WuPaper.ClassicalFourthNat.BPay_567
  · exact WuPaper.ClassicalFourthNat.BPay_568
  · exact WuPaper.ClassicalFourthNat.BPay_569
  · exact WuPaper.ClassicalFourthNat.BPay_570
  · exact WuPaper.ClassicalFourthNat.BPay_571
  · exact WuPaper.ClassicalFourthNat.BPay_572
  · exact WuPaper.ClassicalFourthNat.BPay_573
  · exact WuPaper.ClassicalFourthNat.BPay_574
  · exact WuPaper.ClassicalFourthNat.BPay_575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_008

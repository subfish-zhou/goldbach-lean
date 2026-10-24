import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay118
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_118 (j : Fin 64) (hj : 64*118+j.val < 10540) :
    BPay (64*118+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7552
  · exact WuPaper.ClassicalFourthNat.BPay_7553
  · exact WuPaper.ClassicalFourthNat.BPay_7554
  · exact WuPaper.ClassicalFourthNat.BPay_7555
  · exact WuPaper.ClassicalFourthNat.BPay_7556
  · exact WuPaper.ClassicalFourthNat.BPay_7557
  · exact WuPaper.ClassicalFourthNat.BPay_7558
  · exact WuPaper.ClassicalFourthNat.BPay_7559
  · exact WuPaper.ClassicalFourthNat.BPay_7560
  · exact WuPaper.ClassicalFourthNat.BPay_7561
  · exact WuPaper.ClassicalFourthNat.BPay_7562
  · exact WuPaper.ClassicalFourthNat.BPay_7563
  · exact WuPaper.ClassicalFourthNat.BPay_7564
  · exact WuPaper.ClassicalFourthNat.BPay_7565
  · exact WuPaper.ClassicalFourthNat.BPay_7566
  · exact WuPaper.ClassicalFourthNat.BPay_7567
  · exact WuPaper.ClassicalFourthNat.BPay_7568
  · exact WuPaper.ClassicalFourthNat.BPay_7569
  · exact WuPaper.ClassicalFourthNat.BPay_7570
  · exact WuPaper.ClassicalFourthNat.BPay_7571
  · exact WuPaper.ClassicalFourthNat.BPay_7572
  · exact WuPaper.ClassicalFourthNat.BPay_7573
  · exact WuPaper.ClassicalFourthNat.BPay_7574
  · exact WuPaper.ClassicalFourthNat.BPay_7575
  · exact WuPaper.ClassicalFourthNat.BPay_7576
  · exact WuPaper.ClassicalFourthNat.BPay_7577
  · exact WuPaper.ClassicalFourthNat.BPay_7578
  · exact WuPaper.ClassicalFourthNat.BPay_7579
  · exact WuPaper.ClassicalFourthNat.BPay_7580
  · exact WuPaper.ClassicalFourthNat.BPay_7581
  · exact WuPaper.ClassicalFourthNat.BPay_7582
  · exact WuPaper.ClassicalFourthNat.BPay_7583
  · exact WuPaper.ClassicalFourthNat.BPay_7584
  · exact WuPaper.ClassicalFourthNat.BPay_7585
  · exact WuPaper.ClassicalFourthNat.BPay_7586
  · exact WuPaper.ClassicalFourthNat.BPay_7587
  · exact WuPaper.ClassicalFourthNat.BPay_7588
  · exact WuPaper.ClassicalFourthNat.BPay_7589
  · exact WuPaper.ClassicalFourthNat.BPay_7590
  · exact WuPaper.ClassicalFourthNat.BPay_7591
  · exact WuPaper.ClassicalFourthNat.BPay_7592
  · exact WuPaper.ClassicalFourthNat.BPay_7593
  · exact WuPaper.ClassicalFourthNat.BPay_7594
  · exact WuPaper.ClassicalFourthNat.BPay_7595
  · exact WuPaper.ClassicalFourthNat.BPay_7596
  · exact WuPaper.ClassicalFourthNat.BPay_7597
  · exact WuPaper.ClassicalFourthNat.BPay_7598
  · exact WuPaper.ClassicalFourthNat.BPay_7599
  · exact WuPaper.ClassicalFourthNat.BPay_7600
  · exact WuPaper.ClassicalFourthNat.BPay_7601
  · exact WuPaper.ClassicalFourthNat.BPay_7602
  · exact WuPaper.ClassicalFourthNat.BPay_7603
  · exact WuPaper.ClassicalFourthNat.BPay_7604
  · exact WuPaper.ClassicalFourthNat.BPay_7605
  · exact WuPaper.ClassicalFourthNat.BPay_7606
  · exact WuPaper.ClassicalFourthNat.BPay_7607
  · exact WuPaper.ClassicalFourthNat.BPay_7608
  · exact WuPaper.ClassicalFourthNat.BPay_7609
  · exact WuPaper.ClassicalFourthNat.BPay_7610
  · exact WuPaper.ClassicalFourthNat.BPay_7611
  · exact WuPaper.ClassicalFourthNat.BPay_7612
  · exact WuPaper.ClassicalFourthNat.BPay_7613
  · exact WuPaper.ClassicalFourthNat.BPay_7614
  · exact WuPaper.ClassicalFourthNat.BPay_7615
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_118

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay134
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_134 (j : Fin 64) (hj : 64*134+j.val < 10540) :
    BPay (64*134+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8576
  · exact WuPaper.ClassicalFourthNat.BPay_8577
  · exact WuPaper.ClassicalFourthNat.BPay_8578
  · exact WuPaper.ClassicalFourthNat.BPay_8579
  · exact WuPaper.ClassicalFourthNat.BPay_8580
  · exact WuPaper.ClassicalFourthNat.BPay_8581
  · exact WuPaper.ClassicalFourthNat.BPay_8582
  · exact WuPaper.ClassicalFourthNat.BPay_8583
  · exact WuPaper.ClassicalFourthNat.BPay_8584
  · exact WuPaper.ClassicalFourthNat.BPay_8585
  · exact WuPaper.ClassicalFourthNat.BPay_8586
  · exact WuPaper.ClassicalFourthNat.BPay_8587
  · exact WuPaper.ClassicalFourthNat.BPay_8588
  · exact WuPaper.ClassicalFourthNat.BPay_8589
  · exact WuPaper.ClassicalFourthNat.BPay_8590
  · exact WuPaper.ClassicalFourthNat.BPay_8591
  · exact WuPaper.ClassicalFourthNat.BPay_8592
  · exact WuPaper.ClassicalFourthNat.BPay_8593
  · exact WuPaper.ClassicalFourthNat.BPay_8594
  · exact WuPaper.ClassicalFourthNat.BPay_8595
  · exact WuPaper.ClassicalFourthNat.BPay_8596
  · exact WuPaper.ClassicalFourthNat.BPay_8597
  · exact WuPaper.ClassicalFourthNat.BPay_8598
  · exact WuPaper.ClassicalFourthNat.BPay_8599
  · exact WuPaper.ClassicalFourthNat.BPay_8600
  · exact WuPaper.ClassicalFourthNat.BPay_8601
  · exact WuPaper.ClassicalFourthNat.BPay_8602
  · exact WuPaper.ClassicalFourthNat.BPay_8603
  · exact WuPaper.ClassicalFourthNat.BPay_8604
  · exact WuPaper.ClassicalFourthNat.BPay_8605
  · exact WuPaper.ClassicalFourthNat.BPay_8606
  · exact WuPaper.ClassicalFourthNat.BPay_8607
  · exact WuPaper.ClassicalFourthNat.BPay_8608
  · exact WuPaper.ClassicalFourthNat.BPay_8609
  · exact WuPaper.ClassicalFourthNat.BPay_8610
  · exact WuPaper.ClassicalFourthNat.BPay_8611
  · exact WuPaper.ClassicalFourthNat.BPay_8612
  · exact WuPaper.ClassicalFourthNat.BPay_8613
  · exact WuPaper.ClassicalFourthNat.BPay_8614
  · exact WuPaper.ClassicalFourthNat.BPay_8615
  · exact WuPaper.ClassicalFourthNat.BPay_8616
  · exact WuPaper.ClassicalFourthNat.BPay_8617
  · exact WuPaper.ClassicalFourthNat.BPay_8618
  · exact WuPaper.ClassicalFourthNat.BPay_8619
  · exact WuPaper.ClassicalFourthNat.BPay_8620
  · exact WuPaper.ClassicalFourthNat.BPay_8621
  · exact WuPaper.ClassicalFourthNat.BPay_8622
  · exact WuPaper.ClassicalFourthNat.BPay_8623
  · exact WuPaper.ClassicalFourthNat.BPay_8624
  · exact WuPaper.ClassicalFourthNat.BPay_8625
  · exact WuPaper.ClassicalFourthNat.BPay_8626
  · exact WuPaper.ClassicalFourthNat.BPay_8627
  · exact WuPaper.ClassicalFourthNat.BPay_8628
  · exact WuPaper.ClassicalFourthNat.BPay_8629
  · exact WuPaper.ClassicalFourthNat.BPay_8630
  · exact WuPaper.ClassicalFourthNat.BPay_8631
  · exact WuPaper.ClassicalFourthNat.BPay_8632
  · exact WuPaper.ClassicalFourthNat.BPay_8633
  · exact WuPaper.ClassicalFourthNat.BPay_8634
  · exact WuPaper.ClassicalFourthNat.BPay_8635
  · exact WuPaper.ClassicalFourthNat.BPay_8636
  · exact WuPaper.ClassicalFourthNat.BPay_8637
  · exact WuPaper.ClassicalFourthNat.BPay_8638
  · exact WuPaper.ClassicalFourthNat.BPay_8639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_134

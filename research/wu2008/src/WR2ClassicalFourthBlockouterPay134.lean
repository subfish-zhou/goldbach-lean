import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay134
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_134 (j : Fin 64) (hj : 64*134+j.val < 10540) :
    OuterPay (64*134+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8576
  · exact WuPaper.ClassicalFourthNat.outerPay_8577
  · exact WuPaper.ClassicalFourthNat.outerPay_8578
  · exact WuPaper.ClassicalFourthNat.outerPay_8579
  · exact WuPaper.ClassicalFourthNat.outerPay_8580
  · exact WuPaper.ClassicalFourthNat.outerPay_8581
  · exact WuPaper.ClassicalFourthNat.outerPay_8582
  · exact WuPaper.ClassicalFourthNat.outerPay_8583
  · exact WuPaper.ClassicalFourthNat.outerPay_8584
  · exact WuPaper.ClassicalFourthNat.outerPay_8585
  · exact WuPaper.ClassicalFourthNat.outerPay_8586
  · exact WuPaper.ClassicalFourthNat.outerPay_8587
  · exact WuPaper.ClassicalFourthNat.outerPay_8588
  · exact WuPaper.ClassicalFourthNat.outerPay_8589
  · exact WuPaper.ClassicalFourthNat.outerPay_8590
  · exact WuPaper.ClassicalFourthNat.outerPay_8591
  · exact WuPaper.ClassicalFourthNat.outerPay_8592
  · exact WuPaper.ClassicalFourthNat.outerPay_8593
  · exact WuPaper.ClassicalFourthNat.outerPay_8594
  · exact WuPaper.ClassicalFourthNat.outerPay_8595
  · exact WuPaper.ClassicalFourthNat.outerPay_8596
  · exact WuPaper.ClassicalFourthNat.outerPay_8597
  · exact WuPaper.ClassicalFourthNat.outerPay_8598
  · exact WuPaper.ClassicalFourthNat.outerPay_8599
  · exact WuPaper.ClassicalFourthNat.outerPay_8600
  · exact WuPaper.ClassicalFourthNat.outerPay_8601
  · exact WuPaper.ClassicalFourthNat.outerPay_8602
  · exact WuPaper.ClassicalFourthNat.outerPay_8603
  · exact WuPaper.ClassicalFourthNat.outerPay_8604
  · exact WuPaper.ClassicalFourthNat.outerPay_8605
  · exact WuPaper.ClassicalFourthNat.outerPay_8606
  · exact WuPaper.ClassicalFourthNat.outerPay_8607
  · exact WuPaper.ClassicalFourthNat.outerPay_8608
  · exact WuPaper.ClassicalFourthNat.outerPay_8609
  · exact WuPaper.ClassicalFourthNat.outerPay_8610
  · exact WuPaper.ClassicalFourthNat.outerPay_8611
  · exact WuPaper.ClassicalFourthNat.outerPay_8612
  · exact WuPaper.ClassicalFourthNat.outerPay_8613
  · exact WuPaper.ClassicalFourthNat.outerPay_8614
  · exact WuPaper.ClassicalFourthNat.outerPay_8615
  · exact WuPaper.ClassicalFourthNat.outerPay_8616
  · exact WuPaper.ClassicalFourthNat.outerPay_8617
  · exact WuPaper.ClassicalFourthNat.outerPay_8618
  · exact WuPaper.ClassicalFourthNat.outerPay_8619
  · exact WuPaper.ClassicalFourthNat.outerPay_8620
  · exact WuPaper.ClassicalFourthNat.outerPay_8621
  · exact WuPaper.ClassicalFourthNat.outerPay_8622
  · exact WuPaper.ClassicalFourthNat.outerPay_8623
  · exact WuPaper.ClassicalFourthNat.outerPay_8624
  · exact WuPaper.ClassicalFourthNat.outerPay_8625
  · exact WuPaper.ClassicalFourthNat.outerPay_8626
  · exact WuPaper.ClassicalFourthNat.outerPay_8627
  · exact WuPaper.ClassicalFourthNat.outerPay_8628
  · exact WuPaper.ClassicalFourthNat.outerPay_8629
  · exact WuPaper.ClassicalFourthNat.outerPay_8630
  · exact WuPaper.ClassicalFourthNat.outerPay_8631
  · exact WuPaper.ClassicalFourthNat.outerPay_8632
  · exact WuPaper.ClassicalFourthNat.outerPay_8633
  · exact WuPaper.ClassicalFourthNat.outerPay_8634
  · exact WuPaper.ClassicalFourthNat.outerPay_8635
  · exact WuPaper.ClassicalFourthNat.outerPay_8636
  · exact WuPaper.ClassicalFourthNat.outerPay_8637
  · exact WuPaper.ClassicalFourthNat.outerPay_8638
  · exact WuPaper.ClassicalFourthNat.outerPay_8639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_134

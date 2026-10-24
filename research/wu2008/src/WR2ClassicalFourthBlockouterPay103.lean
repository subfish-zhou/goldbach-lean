import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay103
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_103 (j : Fin 64) (hj : 64*103+j.val < 10540) :
    OuterPay (64*103+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6592
  · exact WuPaper.ClassicalFourthNat.outerPay_6593
  · exact WuPaper.ClassicalFourthNat.outerPay_6594
  · exact WuPaper.ClassicalFourthNat.outerPay_6595
  · exact WuPaper.ClassicalFourthNat.outerPay_6596
  · exact WuPaper.ClassicalFourthNat.outerPay_6597
  · exact WuPaper.ClassicalFourthNat.outerPay_6598
  · exact WuPaper.ClassicalFourthNat.outerPay_6599
  · exact WuPaper.ClassicalFourthNat.outerPay_6600
  · exact WuPaper.ClassicalFourthNat.outerPay_6601
  · exact WuPaper.ClassicalFourthNat.outerPay_6602
  · exact WuPaper.ClassicalFourthNat.outerPay_6603
  · exact WuPaper.ClassicalFourthNat.outerPay_6604
  · exact WuPaper.ClassicalFourthNat.outerPay_6605
  · exact WuPaper.ClassicalFourthNat.outerPay_6606
  · exact WuPaper.ClassicalFourthNat.outerPay_6607
  · exact WuPaper.ClassicalFourthNat.outerPay_6608
  · exact WuPaper.ClassicalFourthNat.outerPay_6609
  · exact WuPaper.ClassicalFourthNat.outerPay_6610
  · exact WuPaper.ClassicalFourthNat.outerPay_6611
  · exact WuPaper.ClassicalFourthNat.outerPay_6612
  · exact WuPaper.ClassicalFourthNat.outerPay_6613
  · exact WuPaper.ClassicalFourthNat.outerPay_6614
  · exact WuPaper.ClassicalFourthNat.outerPay_6615
  · exact WuPaper.ClassicalFourthNat.outerPay_6616
  · exact WuPaper.ClassicalFourthNat.outerPay_6617
  · exact WuPaper.ClassicalFourthNat.outerPay_6618
  · exact WuPaper.ClassicalFourthNat.outerPay_6619
  · exact WuPaper.ClassicalFourthNat.outerPay_6620
  · exact WuPaper.ClassicalFourthNat.outerPay_6621
  · exact WuPaper.ClassicalFourthNat.outerPay_6622
  · exact WuPaper.ClassicalFourthNat.outerPay_6623
  · exact WuPaper.ClassicalFourthNat.outerPay_6624
  · exact WuPaper.ClassicalFourthNat.outerPay_6625
  · exact WuPaper.ClassicalFourthNat.outerPay_6626
  · exact WuPaper.ClassicalFourthNat.outerPay_6627
  · exact WuPaper.ClassicalFourthNat.outerPay_6628
  · exact WuPaper.ClassicalFourthNat.outerPay_6629
  · exact WuPaper.ClassicalFourthNat.outerPay_6630
  · exact WuPaper.ClassicalFourthNat.outerPay_6631
  · exact WuPaper.ClassicalFourthNat.outerPay_6632
  · exact WuPaper.ClassicalFourthNat.outerPay_6633
  · exact WuPaper.ClassicalFourthNat.outerPay_6634
  · exact WuPaper.ClassicalFourthNat.outerPay_6635
  · exact WuPaper.ClassicalFourthNat.outerPay_6636
  · exact WuPaper.ClassicalFourthNat.outerPay_6637
  · exact WuPaper.ClassicalFourthNat.outerPay_6638
  · exact WuPaper.ClassicalFourthNat.outerPay_6639
  · exact WuPaper.ClassicalFourthNat.outerPay_6640
  · exact WuPaper.ClassicalFourthNat.outerPay_6641
  · exact WuPaper.ClassicalFourthNat.outerPay_6642
  · exact WuPaper.ClassicalFourthNat.outerPay_6643
  · exact WuPaper.ClassicalFourthNat.outerPay_6644
  · exact WuPaper.ClassicalFourthNat.outerPay_6645
  · exact WuPaper.ClassicalFourthNat.outerPay_6646
  · exact WuPaper.ClassicalFourthNat.outerPay_6647
  · exact WuPaper.ClassicalFourthNat.outerPay_6648
  · exact WuPaper.ClassicalFourthNat.outerPay_6649
  · exact WuPaper.ClassicalFourthNat.outerPay_6650
  · exact WuPaper.ClassicalFourthNat.outerPay_6651
  · exact WuPaper.ClassicalFourthNat.outerPay_6652
  · exact WuPaper.ClassicalFourthNat.outerPay_6653
  · exact WuPaper.ClassicalFourthNat.outerPay_6654
  · exact WuPaper.ClassicalFourthNat.outerPay_6655
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_103

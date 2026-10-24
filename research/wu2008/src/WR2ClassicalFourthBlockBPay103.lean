import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay103
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_103 (j : Fin 64) (hj : 64*103+j.val < 10540) :
    BPay (64*103+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6592
  · exact WuPaper.ClassicalFourthNat.BPay_6593
  · exact WuPaper.ClassicalFourthNat.BPay_6594
  · exact WuPaper.ClassicalFourthNat.BPay_6595
  · exact WuPaper.ClassicalFourthNat.BPay_6596
  · exact WuPaper.ClassicalFourthNat.BPay_6597
  · exact WuPaper.ClassicalFourthNat.BPay_6598
  · exact WuPaper.ClassicalFourthNat.BPay_6599
  · exact WuPaper.ClassicalFourthNat.BPay_6600
  · exact WuPaper.ClassicalFourthNat.BPay_6601
  · exact WuPaper.ClassicalFourthNat.BPay_6602
  · exact WuPaper.ClassicalFourthNat.BPay_6603
  · exact WuPaper.ClassicalFourthNat.BPay_6604
  · exact WuPaper.ClassicalFourthNat.BPay_6605
  · exact WuPaper.ClassicalFourthNat.BPay_6606
  · exact WuPaper.ClassicalFourthNat.BPay_6607
  · exact WuPaper.ClassicalFourthNat.BPay_6608
  · exact WuPaper.ClassicalFourthNat.BPay_6609
  · exact WuPaper.ClassicalFourthNat.BPay_6610
  · exact WuPaper.ClassicalFourthNat.BPay_6611
  · exact WuPaper.ClassicalFourthNat.BPay_6612
  · exact WuPaper.ClassicalFourthNat.BPay_6613
  · exact WuPaper.ClassicalFourthNat.BPay_6614
  · exact WuPaper.ClassicalFourthNat.BPay_6615
  · exact WuPaper.ClassicalFourthNat.BPay_6616
  · exact WuPaper.ClassicalFourthNat.BPay_6617
  · exact WuPaper.ClassicalFourthNat.BPay_6618
  · exact WuPaper.ClassicalFourthNat.BPay_6619
  · exact WuPaper.ClassicalFourthNat.BPay_6620
  · exact WuPaper.ClassicalFourthNat.BPay_6621
  · exact WuPaper.ClassicalFourthNat.BPay_6622
  · exact WuPaper.ClassicalFourthNat.BPay_6623
  · exact WuPaper.ClassicalFourthNat.BPay_6624
  · exact WuPaper.ClassicalFourthNat.BPay_6625
  · exact WuPaper.ClassicalFourthNat.BPay_6626
  · exact WuPaper.ClassicalFourthNat.BPay_6627
  · exact WuPaper.ClassicalFourthNat.BPay_6628
  · exact WuPaper.ClassicalFourthNat.BPay_6629
  · exact WuPaper.ClassicalFourthNat.BPay_6630
  · exact WuPaper.ClassicalFourthNat.BPay_6631
  · exact WuPaper.ClassicalFourthNat.BPay_6632
  · exact WuPaper.ClassicalFourthNat.BPay_6633
  · exact WuPaper.ClassicalFourthNat.BPay_6634
  · exact WuPaper.ClassicalFourthNat.BPay_6635
  · exact WuPaper.ClassicalFourthNat.BPay_6636
  · exact WuPaper.ClassicalFourthNat.BPay_6637
  · exact WuPaper.ClassicalFourthNat.BPay_6638
  · exact WuPaper.ClassicalFourthNat.BPay_6639
  · exact WuPaper.ClassicalFourthNat.BPay_6640
  · exact WuPaper.ClassicalFourthNat.BPay_6641
  · exact WuPaper.ClassicalFourthNat.BPay_6642
  · exact WuPaper.ClassicalFourthNat.BPay_6643
  · exact WuPaper.ClassicalFourthNat.BPay_6644
  · exact WuPaper.ClassicalFourthNat.BPay_6645
  · exact WuPaper.ClassicalFourthNat.BPay_6646
  · exact WuPaper.ClassicalFourthNat.BPay_6647
  · exact WuPaper.ClassicalFourthNat.BPay_6648
  · exact WuPaper.ClassicalFourthNat.BPay_6649
  · exact WuPaper.ClassicalFourthNat.BPay_6650
  · exact WuPaper.ClassicalFourthNat.BPay_6651
  · exact WuPaper.ClassicalFourthNat.BPay_6652
  · exact WuPaper.ClassicalFourthNat.BPay_6653
  · exact WuPaper.ClassicalFourthNat.BPay_6654
  · exact WuPaper.ClassicalFourthNat.BPay_6655
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_103

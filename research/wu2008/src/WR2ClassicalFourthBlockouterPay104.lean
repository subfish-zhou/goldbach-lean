import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay104
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_104 (j : Fin 64) (hj : 64*104+j.val < 10540) :
    OuterPay (64*104+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6656
  · exact WuPaper.ClassicalFourthNat.outerPay_6657
  · exact WuPaper.ClassicalFourthNat.outerPay_6658
  · exact WuPaper.ClassicalFourthNat.outerPay_6659
  · exact WuPaper.ClassicalFourthNat.outerPay_6660
  · exact WuPaper.ClassicalFourthNat.outerPay_6661
  · exact WuPaper.ClassicalFourthNat.outerPay_6662
  · exact WuPaper.ClassicalFourthNat.outerPay_6663
  · exact WuPaper.ClassicalFourthNat.outerPay_6664
  · exact WuPaper.ClassicalFourthNat.outerPay_6665
  · exact WuPaper.ClassicalFourthNat.outerPay_6666
  · exact WuPaper.ClassicalFourthNat.outerPay_6667
  · exact WuPaper.ClassicalFourthNat.outerPay_6668
  · exact WuPaper.ClassicalFourthNat.outerPay_6669
  · exact WuPaper.ClassicalFourthNat.outerPay_6670
  · exact WuPaper.ClassicalFourthNat.outerPay_6671
  · exact WuPaper.ClassicalFourthNat.outerPay_6672
  · exact WuPaper.ClassicalFourthNat.outerPay_6673
  · exact WuPaper.ClassicalFourthNat.outerPay_6674
  · exact WuPaper.ClassicalFourthNat.outerPay_6675
  · exact WuPaper.ClassicalFourthNat.outerPay_6676
  · exact WuPaper.ClassicalFourthNat.outerPay_6677
  · exact WuPaper.ClassicalFourthNat.outerPay_6678
  · exact WuPaper.ClassicalFourthNat.outerPay_6679
  · exact WuPaper.ClassicalFourthNat.outerPay_6680
  · exact WuPaper.ClassicalFourthNat.outerPay_6681
  · exact WuPaper.ClassicalFourthNat.outerPay_6682
  · exact WuPaper.ClassicalFourthNat.outerPay_6683
  · exact WuPaper.ClassicalFourthNat.outerPay_6684
  · exact WuPaper.ClassicalFourthNat.outerPay_6685
  · exact WuPaper.ClassicalFourthNat.outerPay_6686
  · exact WuPaper.ClassicalFourthNat.outerPay_6687
  · exact WuPaper.ClassicalFourthNat.outerPay_6688
  · exact WuPaper.ClassicalFourthNat.outerPay_6689
  · exact WuPaper.ClassicalFourthNat.outerPay_6690
  · exact WuPaper.ClassicalFourthNat.outerPay_6691
  · exact WuPaper.ClassicalFourthNat.outerPay_6692
  · exact WuPaper.ClassicalFourthNat.outerPay_6693
  · exact WuPaper.ClassicalFourthNat.outerPay_6694
  · exact WuPaper.ClassicalFourthNat.outerPay_6695
  · exact WuPaper.ClassicalFourthNat.outerPay_6696
  · exact WuPaper.ClassicalFourthNat.outerPay_6697
  · exact WuPaper.ClassicalFourthNat.outerPay_6698
  · exact WuPaper.ClassicalFourthNat.outerPay_6699
  · exact WuPaper.ClassicalFourthNat.outerPay_6700
  · exact WuPaper.ClassicalFourthNat.outerPay_6701
  · exact WuPaper.ClassicalFourthNat.outerPay_6702
  · exact WuPaper.ClassicalFourthNat.outerPay_6703
  · exact WuPaper.ClassicalFourthNat.outerPay_6704
  · exact WuPaper.ClassicalFourthNat.outerPay_6705
  · exact WuPaper.ClassicalFourthNat.outerPay_6706
  · exact WuPaper.ClassicalFourthNat.outerPay_6707
  · exact WuPaper.ClassicalFourthNat.outerPay_6708
  · exact WuPaper.ClassicalFourthNat.outerPay_6709
  · exact WuPaper.ClassicalFourthNat.outerPay_6710
  · exact WuPaper.ClassicalFourthNat.outerPay_6711
  · exact WuPaper.ClassicalFourthNat.outerPay_6712
  · exact WuPaper.ClassicalFourthNat.outerPay_6713
  · exact WuPaper.ClassicalFourthNat.outerPay_6714
  · exact WuPaper.ClassicalFourthNat.outerPay_6715
  · exact WuPaper.ClassicalFourthNat.outerPay_6716
  · exact WuPaper.ClassicalFourthNat.outerPay_6717
  · exact WuPaper.ClassicalFourthNat.outerPay_6718
  · exact WuPaper.ClassicalFourthNat.outerPay_6719
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_104

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay104
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_104 (j : Fin 64) (hj : 64*104+j.val < 10540) :
    BPay (64*104+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6656
  · exact WuPaper.ClassicalFourthNat.BPay_6657
  · exact WuPaper.ClassicalFourthNat.BPay_6658
  · exact WuPaper.ClassicalFourthNat.BPay_6659
  · exact WuPaper.ClassicalFourthNat.BPay_6660
  · exact WuPaper.ClassicalFourthNat.BPay_6661
  · exact WuPaper.ClassicalFourthNat.BPay_6662
  · exact WuPaper.ClassicalFourthNat.BPay_6663
  · exact WuPaper.ClassicalFourthNat.BPay_6664
  · exact WuPaper.ClassicalFourthNat.BPay_6665
  · exact WuPaper.ClassicalFourthNat.BPay_6666
  · exact WuPaper.ClassicalFourthNat.BPay_6667
  · exact WuPaper.ClassicalFourthNat.BPay_6668
  · exact WuPaper.ClassicalFourthNat.BPay_6669
  · exact WuPaper.ClassicalFourthNat.BPay_6670
  · exact WuPaper.ClassicalFourthNat.BPay_6671
  · exact WuPaper.ClassicalFourthNat.BPay_6672
  · exact WuPaper.ClassicalFourthNat.BPay_6673
  · exact WuPaper.ClassicalFourthNat.BPay_6674
  · exact WuPaper.ClassicalFourthNat.BPay_6675
  · exact WuPaper.ClassicalFourthNat.BPay_6676
  · exact WuPaper.ClassicalFourthNat.BPay_6677
  · exact WuPaper.ClassicalFourthNat.BPay_6678
  · exact WuPaper.ClassicalFourthNat.BPay_6679
  · exact WuPaper.ClassicalFourthNat.BPay_6680
  · exact WuPaper.ClassicalFourthNat.BPay_6681
  · exact WuPaper.ClassicalFourthNat.BPay_6682
  · exact WuPaper.ClassicalFourthNat.BPay_6683
  · exact WuPaper.ClassicalFourthNat.BPay_6684
  · exact WuPaper.ClassicalFourthNat.BPay_6685
  · exact WuPaper.ClassicalFourthNat.BPay_6686
  · exact WuPaper.ClassicalFourthNat.BPay_6687
  · exact WuPaper.ClassicalFourthNat.BPay_6688
  · exact WuPaper.ClassicalFourthNat.BPay_6689
  · exact WuPaper.ClassicalFourthNat.BPay_6690
  · exact WuPaper.ClassicalFourthNat.BPay_6691
  · exact WuPaper.ClassicalFourthNat.BPay_6692
  · exact WuPaper.ClassicalFourthNat.BPay_6693
  · exact WuPaper.ClassicalFourthNat.BPay_6694
  · exact WuPaper.ClassicalFourthNat.BPay_6695
  · exact WuPaper.ClassicalFourthNat.BPay_6696
  · exact WuPaper.ClassicalFourthNat.BPay_6697
  · exact WuPaper.ClassicalFourthNat.BPay_6698
  · exact WuPaper.ClassicalFourthNat.BPay_6699
  · exact WuPaper.ClassicalFourthNat.BPay_6700
  · exact WuPaper.ClassicalFourthNat.BPay_6701
  · exact WuPaper.ClassicalFourthNat.BPay_6702
  · exact WuPaper.ClassicalFourthNat.BPay_6703
  · exact WuPaper.ClassicalFourthNat.BPay_6704
  · exact WuPaper.ClassicalFourthNat.BPay_6705
  · exact WuPaper.ClassicalFourthNat.BPay_6706
  · exact WuPaper.ClassicalFourthNat.BPay_6707
  · exact WuPaper.ClassicalFourthNat.BPay_6708
  · exact WuPaper.ClassicalFourthNat.BPay_6709
  · exact WuPaper.ClassicalFourthNat.BPay_6710
  · exact WuPaper.ClassicalFourthNat.BPay_6711
  · exact WuPaper.ClassicalFourthNat.BPay_6712
  · exact WuPaper.ClassicalFourthNat.BPay_6713
  · exact WuPaper.ClassicalFourthNat.BPay_6714
  · exact WuPaper.ClassicalFourthNat.BPay_6715
  · exact WuPaper.ClassicalFourthNat.BPay_6716
  · exact WuPaper.ClassicalFourthNat.BPay_6717
  · exact WuPaper.ClassicalFourthNat.BPay_6718
  · exact WuPaper.ClassicalFourthNat.BPay_6719
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_104

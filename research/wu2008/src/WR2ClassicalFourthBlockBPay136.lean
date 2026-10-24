import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay136
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_136 (j : Fin 64) (hj : 64*136+j.val < 10540) :
    BPay (64*136+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8704
  · exact WuPaper.ClassicalFourthNat.BPay_8705
  · exact WuPaper.ClassicalFourthNat.BPay_8706
  · exact WuPaper.ClassicalFourthNat.BPay_8707
  · exact WuPaper.ClassicalFourthNat.BPay_8708
  · exact WuPaper.ClassicalFourthNat.BPay_8709
  · exact WuPaper.ClassicalFourthNat.BPay_8710
  · exact WuPaper.ClassicalFourthNat.BPay_8711
  · exact WuPaper.ClassicalFourthNat.BPay_8712
  · exact WuPaper.ClassicalFourthNat.BPay_8713
  · exact WuPaper.ClassicalFourthNat.BPay_8714
  · exact WuPaper.ClassicalFourthNat.BPay_8715
  · exact WuPaper.ClassicalFourthNat.BPay_8716
  · exact WuPaper.ClassicalFourthNat.BPay_8717
  · exact WuPaper.ClassicalFourthNat.BPay_8718
  · exact WuPaper.ClassicalFourthNat.BPay_8719
  · exact WuPaper.ClassicalFourthNat.BPay_8720
  · exact WuPaper.ClassicalFourthNat.BPay_8721
  · exact WuPaper.ClassicalFourthNat.BPay_8722
  · exact WuPaper.ClassicalFourthNat.BPay_8723
  · exact WuPaper.ClassicalFourthNat.BPay_8724
  · exact WuPaper.ClassicalFourthNat.BPay_8725
  · exact WuPaper.ClassicalFourthNat.BPay_8726
  · exact WuPaper.ClassicalFourthNat.BPay_8727
  · exact WuPaper.ClassicalFourthNat.BPay_8728
  · exact WuPaper.ClassicalFourthNat.BPay_8729
  · exact WuPaper.ClassicalFourthNat.BPay_8730
  · exact WuPaper.ClassicalFourthNat.BPay_8731
  · exact WuPaper.ClassicalFourthNat.BPay_8732
  · exact WuPaper.ClassicalFourthNat.BPay_8733
  · exact WuPaper.ClassicalFourthNat.BPay_8734
  · exact WuPaper.ClassicalFourthNat.BPay_8735
  · exact WuPaper.ClassicalFourthNat.BPay_8736
  · exact WuPaper.ClassicalFourthNat.BPay_8737
  · exact WuPaper.ClassicalFourthNat.BPay_8738
  · exact WuPaper.ClassicalFourthNat.BPay_8739
  · exact WuPaper.ClassicalFourthNat.BPay_8740
  · exact WuPaper.ClassicalFourthNat.BPay_8741
  · exact WuPaper.ClassicalFourthNat.BPay_8742
  · exact WuPaper.ClassicalFourthNat.BPay_8743
  · exact WuPaper.ClassicalFourthNat.BPay_8744
  · exact WuPaper.ClassicalFourthNat.BPay_8745
  · exact WuPaper.ClassicalFourthNat.BPay_8746
  · exact WuPaper.ClassicalFourthNat.BPay_8747
  · exact WuPaper.ClassicalFourthNat.BPay_8748
  · exact WuPaper.ClassicalFourthNat.BPay_8749
  · exact WuPaper.ClassicalFourthNat.BPay_8750
  · exact WuPaper.ClassicalFourthNat.BPay_8751
  · exact WuPaper.ClassicalFourthNat.BPay_8752
  · exact WuPaper.ClassicalFourthNat.BPay_8753
  · exact WuPaper.ClassicalFourthNat.BPay_8754
  · exact WuPaper.ClassicalFourthNat.BPay_8755
  · exact WuPaper.ClassicalFourthNat.BPay_8756
  · exact WuPaper.ClassicalFourthNat.BPay_8757
  · exact WuPaper.ClassicalFourthNat.BPay_8758
  · exact WuPaper.ClassicalFourthNat.BPay_8759
  · exact WuPaper.ClassicalFourthNat.BPay_8760
  · exact WuPaper.ClassicalFourthNat.BPay_8761
  · exact WuPaper.ClassicalFourthNat.BPay_8762
  · exact WuPaper.ClassicalFourthNat.BPay_8763
  · exact WuPaper.ClassicalFourthNat.BPay_8764
  · exact WuPaper.ClassicalFourthNat.BPay_8765
  · exact WuPaper.ClassicalFourthNat.BPay_8766
  · exact WuPaper.ClassicalFourthNat.BPay_8767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_136

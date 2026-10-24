import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay136
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_136 (j : Fin 64) (hj : 64*136+j.val < 10540) :
    OuterPay (64*136+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8704
  · exact WuPaper.ClassicalFourthNat.outerPay_8705
  · exact WuPaper.ClassicalFourthNat.outerPay_8706
  · exact WuPaper.ClassicalFourthNat.outerPay_8707
  · exact WuPaper.ClassicalFourthNat.outerPay_8708
  · exact WuPaper.ClassicalFourthNat.outerPay_8709
  · exact WuPaper.ClassicalFourthNat.outerPay_8710
  · exact WuPaper.ClassicalFourthNat.outerPay_8711
  · exact WuPaper.ClassicalFourthNat.outerPay_8712
  · exact WuPaper.ClassicalFourthNat.outerPay_8713
  · exact WuPaper.ClassicalFourthNat.outerPay_8714
  · exact WuPaper.ClassicalFourthNat.outerPay_8715
  · exact WuPaper.ClassicalFourthNat.outerPay_8716
  · exact WuPaper.ClassicalFourthNat.outerPay_8717
  · exact WuPaper.ClassicalFourthNat.outerPay_8718
  · exact WuPaper.ClassicalFourthNat.outerPay_8719
  · exact WuPaper.ClassicalFourthNat.outerPay_8720
  · exact WuPaper.ClassicalFourthNat.outerPay_8721
  · exact WuPaper.ClassicalFourthNat.outerPay_8722
  · exact WuPaper.ClassicalFourthNat.outerPay_8723
  · exact WuPaper.ClassicalFourthNat.outerPay_8724
  · exact WuPaper.ClassicalFourthNat.outerPay_8725
  · exact WuPaper.ClassicalFourthNat.outerPay_8726
  · exact WuPaper.ClassicalFourthNat.outerPay_8727
  · exact WuPaper.ClassicalFourthNat.outerPay_8728
  · exact WuPaper.ClassicalFourthNat.outerPay_8729
  · exact WuPaper.ClassicalFourthNat.outerPay_8730
  · exact WuPaper.ClassicalFourthNat.outerPay_8731
  · exact WuPaper.ClassicalFourthNat.outerPay_8732
  · exact WuPaper.ClassicalFourthNat.outerPay_8733
  · exact WuPaper.ClassicalFourthNat.outerPay_8734
  · exact WuPaper.ClassicalFourthNat.outerPay_8735
  · exact WuPaper.ClassicalFourthNat.outerPay_8736
  · exact WuPaper.ClassicalFourthNat.outerPay_8737
  · exact WuPaper.ClassicalFourthNat.outerPay_8738
  · exact WuPaper.ClassicalFourthNat.outerPay_8739
  · exact WuPaper.ClassicalFourthNat.outerPay_8740
  · exact WuPaper.ClassicalFourthNat.outerPay_8741
  · exact WuPaper.ClassicalFourthNat.outerPay_8742
  · exact WuPaper.ClassicalFourthNat.outerPay_8743
  · exact WuPaper.ClassicalFourthNat.outerPay_8744
  · exact WuPaper.ClassicalFourthNat.outerPay_8745
  · exact WuPaper.ClassicalFourthNat.outerPay_8746
  · exact WuPaper.ClassicalFourthNat.outerPay_8747
  · exact WuPaper.ClassicalFourthNat.outerPay_8748
  · exact WuPaper.ClassicalFourthNat.outerPay_8749
  · exact WuPaper.ClassicalFourthNat.outerPay_8750
  · exact WuPaper.ClassicalFourthNat.outerPay_8751
  · exact WuPaper.ClassicalFourthNat.outerPay_8752
  · exact WuPaper.ClassicalFourthNat.outerPay_8753
  · exact WuPaper.ClassicalFourthNat.outerPay_8754
  · exact WuPaper.ClassicalFourthNat.outerPay_8755
  · exact WuPaper.ClassicalFourthNat.outerPay_8756
  · exact WuPaper.ClassicalFourthNat.outerPay_8757
  · exact WuPaper.ClassicalFourthNat.outerPay_8758
  · exact WuPaper.ClassicalFourthNat.outerPay_8759
  · exact WuPaper.ClassicalFourthNat.outerPay_8760
  · exact WuPaper.ClassicalFourthNat.outerPay_8761
  · exact WuPaper.ClassicalFourthNat.outerPay_8762
  · exact WuPaper.ClassicalFourthNat.outerPay_8763
  · exact WuPaper.ClassicalFourthNat.outerPay_8764
  · exact WuPaper.ClassicalFourthNat.outerPay_8765
  · exact WuPaper.ClassicalFourthNat.outerPay_8766
  · exact WuPaper.ClassicalFourthNat.outerPay_8767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_136

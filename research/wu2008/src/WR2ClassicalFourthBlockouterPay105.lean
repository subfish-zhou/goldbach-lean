import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay105
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_105 (j : Fin 64) (hj : 64*105+j.val < 10540) :
    OuterPay (64*105+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6720
  · exact WuPaper.ClassicalFourthNat.outerPay_6721
  · exact WuPaper.ClassicalFourthNat.outerPay_6722
  · exact WuPaper.ClassicalFourthNat.outerPay_6723
  · exact WuPaper.ClassicalFourthNat.outerPay_6724
  · exact WuPaper.ClassicalFourthNat.outerPay_6725
  · exact WuPaper.ClassicalFourthNat.outerPay_6726
  · exact WuPaper.ClassicalFourthNat.outerPay_6727
  · exact WuPaper.ClassicalFourthNat.outerPay_6728
  · exact WuPaper.ClassicalFourthNat.outerPay_6729
  · exact WuPaper.ClassicalFourthNat.outerPay_6730
  · exact WuPaper.ClassicalFourthNat.outerPay_6731
  · exact WuPaper.ClassicalFourthNat.outerPay_6732
  · exact WuPaper.ClassicalFourthNat.outerPay_6733
  · exact WuPaper.ClassicalFourthNat.outerPay_6734
  · exact WuPaper.ClassicalFourthNat.outerPay_6735
  · exact WuPaper.ClassicalFourthNat.outerPay_6736
  · exact WuPaper.ClassicalFourthNat.outerPay_6737
  · exact WuPaper.ClassicalFourthNat.outerPay_6738
  · exact WuPaper.ClassicalFourthNat.outerPay_6739
  · exact WuPaper.ClassicalFourthNat.outerPay_6740
  · exact WuPaper.ClassicalFourthNat.outerPay_6741
  · exact WuPaper.ClassicalFourthNat.outerPay_6742
  · exact WuPaper.ClassicalFourthNat.outerPay_6743
  · exact WuPaper.ClassicalFourthNat.outerPay_6744
  · exact WuPaper.ClassicalFourthNat.outerPay_6745
  · exact WuPaper.ClassicalFourthNat.outerPay_6746
  · exact WuPaper.ClassicalFourthNat.outerPay_6747
  · exact WuPaper.ClassicalFourthNat.outerPay_6748
  · exact WuPaper.ClassicalFourthNat.outerPay_6749
  · exact WuPaper.ClassicalFourthNat.outerPay_6750
  · exact WuPaper.ClassicalFourthNat.outerPay_6751
  · exact WuPaper.ClassicalFourthNat.outerPay_6752
  · exact WuPaper.ClassicalFourthNat.outerPay_6753
  · exact WuPaper.ClassicalFourthNat.outerPay_6754
  · exact WuPaper.ClassicalFourthNat.outerPay_6755
  · exact WuPaper.ClassicalFourthNat.outerPay_6756
  · exact WuPaper.ClassicalFourthNat.outerPay_6757
  · exact WuPaper.ClassicalFourthNat.outerPay_6758
  · exact WuPaper.ClassicalFourthNat.outerPay_6759
  · exact WuPaper.ClassicalFourthNat.outerPay_6760
  · exact WuPaper.ClassicalFourthNat.outerPay_6761
  · exact WuPaper.ClassicalFourthNat.outerPay_6762
  · exact WuPaper.ClassicalFourthNat.outerPay_6763
  · exact WuPaper.ClassicalFourthNat.outerPay_6764
  · exact WuPaper.ClassicalFourthNat.outerPay_6765
  · exact WuPaper.ClassicalFourthNat.outerPay_6766
  · exact WuPaper.ClassicalFourthNat.outerPay_6767
  · exact WuPaper.ClassicalFourthNat.outerPay_6768
  · exact WuPaper.ClassicalFourthNat.outerPay_6769
  · exact WuPaper.ClassicalFourthNat.outerPay_6770
  · exact WuPaper.ClassicalFourthNat.outerPay_6771
  · exact WuPaper.ClassicalFourthNat.outerPay_6772
  · exact WuPaper.ClassicalFourthNat.outerPay_6773
  · exact WuPaper.ClassicalFourthNat.outerPay_6774
  · exact WuPaper.ClassicalFourthNat.outerPay_6775
  · exact WuPaper.ClassicalFourthNat.outerPay_6776
  · exact WuPaper.ClassicalFourthNat.outerPay_6777
  · exact WuPaper.ClassicalFourthNat.outerPay_6778
  · exact WuPaper.ClassicalFourthNat.outerPay_6779
  · exact WuPaper.ClassicalFourthNat.outerPay_6780
  · exact WuPaper.ClassicalFourthNat.outerPay_6781
  · exact WuPaper.ClassicalFourthNat.outerPay_6782
  · exact WuPaper.ClassicalFourthNat.outerPay_6783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_105

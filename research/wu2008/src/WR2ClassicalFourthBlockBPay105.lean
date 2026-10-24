import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay105
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_105 (j : Fin 64) (hj : 64*105+j.val < 10540) :
    BPay (64*105+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6720
  · exact WuPaper.ClassicalFourthNat.BPay_6721
  · exact WuPaper.ClassicalFourthNat.BPay_6722
  · exact WuPaper.ClassicalFourthNat.BPay_6723
  · exact WuPaper.ClassicalFourthNat.BPay_6724
  · exact WuPaper.ClassicalFourthNat.BPay_6725
  · exact WuPaper.ClassicalFourthNat.BPay_6726
  · exact WuPaper.ClassicalFourthNat.BPay_6727
  · exact WuPaper.ClassicalFourthNat.BPay_6728
  · exact WuPaper.ClassicalFourthNat.BPay_6729
  · exact WuPaper.ClassicalFourthNat.BPay_6730
  · exact WuPaper.ClassicalFourthNat.BPay_6731
  · exact WuPaper.ClassicalFourthNat.BPay_6732
  · exact WuPaper.ClassicalFourthNat.BPay_6733
  · exact WuPaper.ClassicalFourthNat.BPay_6734
  · exact WuPaper.ClassicalFourthNat.BPay_6735
  · exact WuPaper.ClassicalFourthNat.BPay_6736
  · exact WuPaper.ClassicalFourthNat.BPay_6737
  · exact WuPaper.ClassicalFourthNat.BPay_6738
  · exact WuPaper.ClassicalFourthNat.BPay_6739
  · exact WuPaper.ClassicalFourthNat.BPay_6740
  · exact WuPaper.ClassicalFourthNat.BPay_6741
  · exact WuPaper.ClassicalFourthNat.BPay_6742
  · exact WuPaper.ClassicalFourthNat.BPay_6743
  · exact WuPaper.ClassicalFourthNat.BPay_6744
  · exact WuPaper.ClassicalFourthNat.BPay_6745
  · exact WuPaper.ClassicalFourthNat.BPay_6746
  · exact WuPaper.ClassicalFourthNat.BPay_6747
  · exact WuPaper.ClassicalFourthNat.BPay_6748
  · exact WuPaper.ClassicalFourthNat.BPay_6749
  · exact WuPaper.ClassicalFourthNat.BPay_6750
  · exact WuPaper.ClassicalFourthNat.BPay_6751
  · exact WuPaper.ClassicalFourthNat.BPay_6752
  · exact WuPaper.ClassicalFourthNat.BPay_6753
  · exact WuPaper.ClassicalFourthNat.BPay_6754
  · exact WuPaper.ClassicalFourthNat.BPay_6755
  · exact WuPaper.ClassicalFourthNat.BPay_6756
  · exact WuPaper.ClassicalFourthNat.BPay_6757
  · exact WuPaper.ClassicalFourthNat.BPay_6758
  · exact WuPaper.ClassicalFourthNat.BPay_6759
  · exact WuPaper.ClassicalFourthNat.BPay_6760
  · exact WuPaper.ClassicalFourthNat.BPay_6761
  · exact WuPaper.ClassicalFourthNat.BPay_6762
  · exact WuPaper.ClassicalFourthNat.BPay_6763
  · exact WuPaper.ClassicalFourthNat.BPay_6764
  · exact WuPaper.ClassicalFourthNat.BPay_6765
  · exact WuPaper.ClassicalFourthNat.BPay_6766
  · exact WuPaper.ClassicalFourthNat.BPay_6767
  · exact WuPaper.ClassicalFourthNat.BPay_6768
  · exact WuPaper.ClassicalFourthNat.BPay_6769
  · exact WuPaper.ClassicalFourthNat.BPay_6770
  · exact WuPaper.ClassicalFourthNat.BPay_6771
  · exact WuPaper.ClassicalFourthNat.BPay_6772
  · exact WuPaper.ClassicalFourthNat.BPay_6773
  · exact WuPaper.ClassicalFourthNat.BPay_6774
  · exact WuPaper.ClassicalFourthNat.BPay_6775
  · exact WuPaper.ClassicalFourthNat.BPay_6776
  · exact WuPaper.ClassicalFourthNat.BPay_6777
  · exact WuPaper.ClassicalFourthNat.BPay_6778
  · exact WuPaper.ClassicalFourthNat.BPay_6779
  · exact WuPaper.ClassicalFourthNat.BPay_6780
  · exact WuPaper.ClassicalFourthNat.BPay_6781
  · exact WuPaper.ClassicalFourthNat.BPay_6782
  · exact WuPaper.ClassicalFourthNat.BPay_6783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_105

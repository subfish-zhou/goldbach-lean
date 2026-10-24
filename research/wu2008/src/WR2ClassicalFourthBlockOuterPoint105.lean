import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint105
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_105 (j : Fin 64) (hj : 64*105+j.val < 10541) :
    OuterPoint (64*105+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6720
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6721
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6722
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6723
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6724
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6725
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6726
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6727
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6728
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6729
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6730
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6731
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6732
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6733
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6734
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6735
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6736
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6737
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6738
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6739
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6740
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6741
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6742
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6743
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6744
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6745
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6746
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6747
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6748
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6749
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6750
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6751
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6752
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6753
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6754
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6755
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6756
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6757
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6758
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6759
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6760
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6761
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6762
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6763
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6764
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6765
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6766
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6767
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6768
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6769
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6770
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6771
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6772
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6773
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6774
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6775
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6776
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6777
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6778
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6779
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6780
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6781
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6782
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_105

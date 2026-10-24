import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint106
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_106 (j : Fin 64) (hj : 64*106+j.val < 10541) :
    OuterPoint (64*106+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6784
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6785
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6786
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6787
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6788
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6789
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6790
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6791
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6792
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6793
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6794
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6795
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6796
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6797
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6798
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6799
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6800
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6801
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6802
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6803
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6804
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6805
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6806
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6807
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6808
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6809
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6810
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6811
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6812
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6813
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6814
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6815
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6816
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6817
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6818
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6819
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6820
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6821
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6822
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6823
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6824
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6825
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6826
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6827
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6828
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6829
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6830
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6831
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6832
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6833
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6834
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6835
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6836
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6837
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6838
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6839
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6840
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6841
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6842
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6843
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6844
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6845
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6846
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_106

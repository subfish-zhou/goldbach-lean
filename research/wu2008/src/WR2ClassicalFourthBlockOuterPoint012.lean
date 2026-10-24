import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint012
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_012 (j : Fin 64) (hj : 64*12+j.val < 10541) :
    OuterPoint (64*12+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_768
  · exact WuPaper.ClassicalFourthNat.OuterPoint_769
  · exact WuPaper.ClassicalFourthNat.OuterPoint_770
  · exact WuPaper.ClassicalFourthNat.OuterPoint_771
  · exact WuPaper.ClassicalFourthNat.OuterPoint_772
  · exact WuPaper.ClassicalFourthNat.OuterPoint_773
  · exact WuPaper.ClassicalFourthNat.OuterPoint_774
  · exact WuPaper.ClassicalFourthNat.OuterPoint_775
  · exact WuPaper.ClassicalFourthNat.OuterPoint_776
  · exact WuPaper.ClassicalFourthNat.OuterPoint_777
  · exact WuPaper.ClassicalFourthNat.OuterPoint_778
  · exact WuPaper.ClassicalFourthNat.OuterPoint_779
  · exact WuPaper.ClassicalFourthNat.OuterPoint_780
  · exact WuPaper.ClassicalFourthNat.OuterPoint_781
  · exact WuPaper.ClassicalFourthNat.OuterPoint_782
  · exact WuPaper.ClassicalFourthNat.OuterPoint_783
  · exact WuPaper.ClassicalFourthNat.OuterPoint_784
  · exact WuPaper.ClassicalFourthNat.OuterPoint_785
  · exact WuPaper.ClassicalFourthNat.OuterPoint_786
  · exact WuPaper.ClassicalFourthNat.OuterPoint_787
  · exact WuPaper.ClassicalFourthNat.OuterPoint_788
  · exact WuPaper.ClassicalFourthNat.OuterPoint_789
  · exact WuPaper.ClassicalFourthNat.OuterPoint_790
  · exact WuPaper.ClassicalFourthNat.OuterPoint_791
  · exact WuPaper.ClassicalFourthNat.OuterPoint_792
  · exact WuPaper.ClassicalFourthNat.OuterPoint_793
  · exact WuPaper.ClassicalFourthNat.OuterPoint_794
  · exact WuPaper.ClassicalFourthNat.OuterPoint_795
  · exact WuPaper.ClassicalFourthNat.OuterPoint_796
  · exact WuPaper.ClassicalFourthNat.OuterPoint_797
  · exact WuPaper.ClassicalFourthNat.OuterPoint_798
  · exact WuPaper.ClassicalFourthNat.OuterPoint_799
  · exact WuPaper.ClassicalFourthNat.OuterPoint_800
  · exact WuPaper.ClassicalFourthNat.OuterPoint_801
  · exact WuPaper.ClassicalFourthNat.OuterPoint_802
  · exact WuPaper.ClassicalFourthNat.OuterPoint_803
  · exact WuPaper.ClassicalFourthNat.OuterPoint_804
  · exact WuPaper.ClassicalFourthNat.OuterPoint_805
  · exact WuPaper.ClassicalFourthNat.OuterPoint_806
  · exact WuPaper.ClassicalFourthNat.OuterPoint_807
  · exact WuPaper.ClassicalFourthNat.OuterPoint_808
  · exact WuPaper.ClassicalFourthNat.OuterPoint_809
  · exact WuPaper.ClassicalFourthNat.OuterPoint_810
  · exact WuPaper.ClassicalFourthNat.OuterPoint_811
  · exact WuPaper.ClassicalFourthNat.OuterPoint_812
  · exact WuPaper.ClassicalFourthNat.OuterPoint_813
  · exact WuPaper.ClassicalFourthNat.OuterPoint_814
  · exact WuPaper.ClassicalFourthNat.OuterPoint_815
  · exact WuPaper.ClassicalFourthNat.OuterPoint_816
  · exact WuPaper.ClassicalFourthNat.OuterPoint_817
  · exact WuPaper.ClassicalFourthNat.OuterPoint_818
  · exact WuPaper.ClassicalFourthNat.OuterPoint_819
  · exact WuPaper.ClassicalFourthNat.OuterPoint_820
  · exact WuPaper.ClassicalFourthNat.OuterPoint_821
  · exact WuPaper.ClassicalFourthNat.OuterPoint_822
  · exact WuPaper.ClassicalFourthNat.OuterPoint_823
  · exact WuPaper.ClassicalFourthNat.OuterPoint_824
  · exact WuPaper.ClassicalFourthNat.OuterPoint_825
  · exact WuPaper.ClassicalFourthNat.OuterPoint_826
  · exact WuPaper.ClassicalFourthNat.OuterPoint_827
  · exact WuPaper.ClassicalFourthNat.OuterPoint_828
  · exact WuPaper.ClassicalFourthNat.OuterPoint_829
  · exact WuPaper.ClassicalFourthNat.OuterPoint_830
  · exact WuPaper.ClassicalFourthNat.OuterPoint_831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_012

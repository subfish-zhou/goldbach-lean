import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay012
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_012 (j : Fin 64) (hj : 64*12+j.val < 2540) :
    CPay (64*12+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_768
  · exact WuPaper.ClassicalFourthNat.CPay_769
  · exact WuPaper.ClassicalFourthNat.CPay_770
  · exact WuPaper.ClassicalFourthNat.CPay_771
  · exact WuPaper.ClassicalFourthNat.CPay_772
  · exact WuPaper.ClassicalFourthNat.CPay_773
  · exact WuPaper.ClassicalFourthNat.CPay_774
  · exact WuPaper.ClassicalFourthNat.CPay_775
  · exact WuPaper.ClassicalFourthNat.CPay_776
  · exact WuPaper.ClassicalFourthNat.CPay_777
  · exact WuPaper.ClassicalFourthNat.CPay_778
  · exact WuPaper.ClassicalFourthNat.CPay_779
  · exact WuPaper.ClassicalFourthNat.CPay_780
  · exact WuPaper.ClassicalFourthNat.CPay_781
  · exact WuPaper.ClassicalFourthNat.CPay_782
  · exact WuPaper.ClassicalFourthNat.CPay_783
  · exact WuPaper.ClassicalFourthNat.CPay_784
  · exact WuPaper.ClassicalFourthNat.CPay_785
  · exact WuPaper.ClassicalFourthNat.CPay_786
  · exact WuPaper.ClassicalFourthNat.CPay_787
  · exact WuPaper.ClassicalFourthNat.CPay_788
  · exact WuPaper.ClassicalFourthNat.CPay_789
  · exact WuPaper.ClassicalFourthNat.CPay_790
  · exact WuPaper.ClassicalFourthNat.CPay_791
  · exact WuPaper.ClassicalFourthNat.CPay_792
  · exact WuPaper.ClassicalFourthNat.CPay_793
  · exact WuPaper.ClassicalFourthNat.CPay_794
  · exact WuPaper.ClassicalFourthNat.CPay_795
  · exact WuPaper.ClassicalFourthNat.CPay_796
  · exact WuPaper.ClassicalFourthNat.CPay_797
  · exact WuPaper.ClassicalFourthNat.CPay_798
  · exact WuPaper.ClassicalFourthNat.CPay_799
  · exact WuPaper.ClassicalFourthNat.CPay_800
  · exact WuPaper.ClassicalFourthNat.CPay_801
  · exact WuPaper.ClassicalFourthNat.CPay_802
  · exact WuPaper.ClassicalFourthNat.CPay_803
  · exact WuPaper.ClassicalFourthNat.CPay_804
  · exact WuPaper.ClassicalFourthNat.CPay_805
  · exact WuPaper.ClassicalFourthNat.CPay_806
  · exact WuPaper.ClassicalFourthNat.CPay_807
  · exact WuPaper.ClassicalFourthNat.CPay_808
  · exact WuPaper.ClassicalFourthNat.CPay_809
  · exact WuPaper.ClassicalFourthNat.CPay_810
  · exact WuPaper.ClassicalFourthNat.CPay_811
  · exact WuPaper.ClassicalFourthNat.CPay_812
  · exact WuPaper.ClassicalFourthNat.CPay_813
  · exact WuPaper.ClassicalFourthNat.CPay_814
  · exact WuPaper.ClassicalFourthNat.CPay_815
  · exact WuPaper.ClassicalFourthNat.CPay_816
  · exact WuPaper.ClassicalFourthNat.CPay_817
  · exact WuPaper.ClassicalFourthNat.CPay_818
  · exact WuPaper.ClassicalFourthNat.CPay_819
  · exact WuPaper.ClassicalFourthNat.CPay_820
  · exact WuPaper.ClassicalFourthNat.CPay_821
  · exact WuPaper.ClassicalFourthNat.CPay_822
  · exact WuPaper.ClassicalFourthNat.CPay_823
  · exact WuPaper.ClassicalFourthNat.CPay_824
  · exact WuPaper.ClassicalFourthNat.CPay_825
  · exact WuPaper.ClassicalFourthNat.CPay_826
  · exact WuPaper.ClassicalFourthNat.CPay_827
  · exact WuPaper.ClassicalFourthNat.CPay_828
  · exact WuPaper.ClassicalFourthNat.CPay_829
  · exact WuPaper.ClassicalFourthNat.CPay_830
  · exact WuPaper.ClassicalFourthNat.CPay_831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_012

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay012
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_012 (j : Fin 64) (hj : 64*12+j.val < 10540) :
    OuterPay (64*12+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_768
  · exact WuPaper.ClassicalFourthNat.outerPay_769
  · exact WuPaper.ClassicalFourthNat.outerPay_770
  · exact WuPaper.ClassicalFourthNat.outerPay_771
  · exact WuPaper.ClassicalFourthNat.outerPay_772
  · exact WuPaper.ClassicalFourthNat.outerPay_773
  · exact WuPaper.ClassicalFourthNat.outerPay_774
  · exact WuPaper.ClassicalFourthNat.outerPay_775
  · exact WuPaper.ClassicalFourthNat.outerPay_776
  · exact WuPaper.ClassicalFourthNat.outerPay_777
  · exact WuPaper.ClassicalFourthNat.outerPay_778
  · exact WuPaper.ClassicalFourthNat.outerPay_779
  · exact WuPaper.ClassicalFourthNat.outerPay_780
  · exact WuPaper.ClassicalFourthNat.outerPay_781
  · exact WuPaper.ClassicalFourthNat.outerPay_782
  · exact WuPaper.ClassicalFourthNat.outerPay_783
  · exact WuPaper.ClassicalFourthNat.outerPay_784
  · exact WuPaper.ClassicalFourthNat.outerPay_785
  · exact WuPaper.ClassicalFourthNat.outerPay_786
  · exact WuPaper.ClassicalFourthNat.outerPay_787
  · exact WuPaper.ClassicalFourthNat.outerPay_788
  · exact WuPaper.ClassicalFourthNat.outerPay_789
  · exact WuPaper.ClassicalFourthNat.outerPay_790
  · exact WuPaper.ClassicalFourthNat.outerPay_791
  · exact WuPaper.ClassicalFourthNat.outerPay_792
  · exact WuPaper.ClassicalFourthNat.outerPay_793
  · exact WuPaper.ClassicalFourthNat.outerPay_794
  · exact WuPaper.ClassicalFourthNat.outerPay_795
  · exact WuPaper.ClassicalFourthNat.outerPay_796
  · exact WuPaper.ClassicalFourthNat.outerPay_797
  · exact WuPaper.ClassicalFourthNat.outerPay_798
  · exact WuPaper.ClassicalFourthNat.outerPay_799
  · exact WuPaper.ClassicalFourthNat.outerPay_800
  · exact WuPaper.ClassicalFourthNat.outerPay_801
  · exact WuPaper.ClassicalFourthNat.outerPay_802
  · exact WuPaper.ClassicalFourthNat.outerPay_803
  · exact WuPaper.ClassicalFourthNat.outerPay_804
  · exact WuPaper.ClassicalFourthNat.outerPay_805
  · exact WuPaper.ClassicalFourthNat.outerPay_806
  · exact WuPaper.ClassicalFourthNat.outerPay_807
  · exact WuPaper.ClassicalFourthNat.outerPay_808
  · exact WuPaper.ClassicalFourthNat.outerPay_809
  · exact WuPaper.ClassicalFourthNat.outerPay_810
  · exact WuPaper.ClassicalFourthNat.outerPay_811
  · exact WuPaper.ClassicalFourthNat.outerPay_812
  · exact WuPaper.ClassicalFourthNat.outerPay_813
  · exact WuPaper.ClassicalFourthNat.outerPay_814
  · exact WuPaper.ClassicalFourthNat.outerPay_815
  · exact WuPaper.ClassicalFourthNat.outerPay_816
  · exact WuPaper.ClassicalFourthNat.outerPay_817
  · exact WuPaper.ClassicalFourthNat.outerPay_818
  · exact WuPaper.ClassicalFourthNat.outerPay_819
  · exact WuPaper.ClassicalFourthNat.outerPay_820
  · exact WuPaper.ClassicalFourthNat.outerPay_821
  · exact WuPaper.ClassicalFourthNat.outerPay_822
  · exact WuPaper.ClassicalFourthNat.outerPay_823
  · exact WuPaper.ClassicalFourthNat.outerPay_824
  · exact WuPaper.ClassicalFourthNat.outerPay_825
  · exact WuPaper.ClassicalFourthNat.outerPay_826
  · exact WuPaper.ClassicalFourthNat.outerPay_827
  · exact WuPaper.ClassicalFourthNat.outerPay_828
  · exact WuPaper.ClassicalFourthNat.outerPay_829
  · exact WuPaper.ClassicalFourthNat.outerPay_830
  · exact WuPaper.ClassicalFourthNat.outerPay_831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_012

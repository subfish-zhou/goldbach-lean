import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay012
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_012 (j : Fin 64) (hj : 64*12+j.val < 2540) :
    DPay (64*12+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_768
  · exact WuPaper.ClassicalFourthNat.DPay_769
  · exact WuPaper.ClassicalFourthNat.DPay_770
  · exact WuPaper.ClassicalFourthNat.DPay_771
  · exact WuPaper.ClassicalFourthNat.DPay_772
  · exact WuPaper.ClassicalFourthNat.DPay_773
  · exact WuPaper.ClassicalFourthNat.DPay_774
  · exact WuPaper.ClassicalFourthNat.DPay_775
  · exact WuPaper.ClassicalFourthNat.DPay_776
  · exact WuPaper.ClassicalFourthNat.DPay_777
  · exact WuPaper.ClassicalFourthNat.DPay_778
  · exact WuPaper.ClassicalFourthNat.DPay_779
  · exact WuPaper.ClassicalFourthNat.DPay_780
  · exact WuPaper.ClassicalFourthNat.DPay_781
  · exact WuPaper.ClassicalFourthNat.DPay_782
  · exact WuPaper.ClassicalFourthNat.DPay_783
  · exact WuPaper.ClassicalFourthNat.DPay_784
  · exact WuPaper.ClassicalFourthNat.DPay_785
  · exact WuPaper.ClassicalFourthNat.DPay_786
  · exact WuPaper.ClassicalFourthNat.DPay_787
  · exact WuPaper.ClassicalFourthNat.DPay_788
  · exact WuPaper.ClassicalFourthNat.DPay_789
  · exact WuPaper.ClassicalFourthNat.DPay_790
  · exact WuPaper.ClassicalFourthNat.DPay_791
  · exact WuPaper.ClassicalFourthNat.DPay_792
  · exact WuPaper.ClassicalFourthNat.DPay_793
  · exact WuPaper.ClassicalFourthNat.DPay_794
  · exact WuPaper.ClassicalFourthNat.DPay_795
  · exact WuPaper.ClassicalFourthNat.DPay_796
  · exact WuPaper.ClassicalFourthNat.DPay_797
  · exact WuPaper.ClassicalFourthNat.DPay_798
  · exact WuPaper.ClassicalFourthNat.DPay_799
  · exact WuPaper.ClassicalFourthNat.DPay_800
  · exact WuPaper.ClassicalFourthNat.DPay_801
  · exact WuPaper.ClassicalFourthNat.DPay_802
  · exact WuPaper.ClassicalFourthNat.DPay_803
  · exact WuPaper.ClassicalFourthNat.DPay_804
  · exact WuPaper.ClassicalFourthNat.DPay_805
  · exact WuPaper.ClassicalFourthNat.DPay_806
  · exact WuPaper.ClassicalFourthNat.DPay_807
  · exact WuPaper.ClassicalFourthNat.DPay_808
  · exact WuPaper.ClassicalFourthNat.DPay_809
  · exact WuPaper.ClassicalFourthNat.DPay_810
  · exact WuPaper.ClassicalFourthNat.DPay_811
  · exact WuPaper.ClassicalFourthNat.DPay_812
  · exact WuPaper.ClassicalFourthNat.DPay_813
  · exact WuPaper.ClassicalFourthNat.DPay_814
  · exact WuPaper.ClassicalFourthNat.DPay_815
  · exact WuPaper.ClassicalFourthNat.DPay_816
  · exact WuPaper.ClassicalFourthNat.DPay_817
  · exact WuPaper.ClassicalFourthNat.DPay_818
  · exact WuPaper.ClassicalFourthNat.DPay_819
  · exact WuPaper.ClassicalFourthNat.DPay_820
  · exact WuPaper.ClassicalFourthNat.DPay_821
  · exact WuPaper.ClassicalFourthNat.DPay_822
  · exact WuPaper.ClassicalFourthNat.DPay_823
  · exact WuPaper.ClassicalFourthNat.DPay_824
  · exact WuPaper.ClassicalFourthNat.DPay_825
  · exact WuPaper.ClassicalFourthNat.DPay_826
  · exact WuPaper.ClassicalFourthNat.DPay_827
  · exact WuPaper.ClassicalFourthNat.DPay_828
  · exact WuPaper.ClassicalFourthNat.DPay_829
  · exact WuPaper.ClassicalFourthNat.DPay_830
  · exact WuPaper.ClassicalFourthNat.DPay_831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_012

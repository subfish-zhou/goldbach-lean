import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay012
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_012 (j : Fin 64) (hj : 64*12+j.val < 10540) :
    BPay (64*12+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_768
  · exact WuPaper.ClassicalFourthNat.BPay_769
  · exact WuPaper.ClassicalFourthNat.BPay_770
  · exact WuPaper.ClassicalFourthNat.BPay_771
  · exact WuPaper.ClassicalFourthNat.BPay_772
  · exact WuPaper.ClassicalFourthNat.BPay_773
  · exact WuPaper.ClassicalFourthNat.BPay_774
  · exact WuPaper.ClassicalFourthNat.BPay_775
  · exact WuPaper.ClassicalFourthNat.BPay_776
  · exact WuPaper.ClassicalFourthNat.BPay_777
  · exact WuPaper.ClassicalFourthNat.BPay_778
  · exact WuPaper.ClassicalFourthNat.BPay_779
  · exact WuPaper.ClassicalFourthNat.BPay_780
  · exact WuPaper.ClassicalFourthNat.BPay_781
  · exact WuPaper.ClassicalFourthNat.BPay_782
  · exact WuPaper.ClassicalFourthNat.BPay_783
  · exact WuPaper.ClassicalFourthNat.BPay_784
  · exact WuPaper.ClassicalFourthNat.BPay_785
  · exact WuPaper.ClassicalFourthNat.BPay_786
  · exact WuPaper.ClassicalFourthNat.BPay_787
  · exact WuPaper.ClassicalFourthNat.BPay_788
  · exact WuPaper.ClassicalFourthNat.BPay_789
  · exact WuPaper.ClassicalFourthNat.BPay_790
  · exact WuPaper.ClassicalFourthNat.BPay_791
  · exact WuPaper.ClassicalFourthNat.BPay_792
  · exact WuPaper.ClassicalFourthNat.BPay_793
  · exact WuPaper.ClassicalFourthNat.BPay_794
  · exact WuPaper.ClassicalFourthNat.BPay_795
  · exact WuPaper.ClassicalFourthNat.BPay_796
  · exact WuPaper.ClassicalFourthNat.BPay_797
  · exact WuPaper.ClassicalFourthNat.BPay_798
  · exact WuPaper.ClassicalFourthNat.BPay_799
  · exact WuPaper.ClassicalFourthNat.BPay_800
  · exact WuPaper.ClassicalFourthNat.BPay_801
  · exact WuPaper.ClassicalFourthNat.BPay_802
  · exact WuPaper.ClassicalFourthNat.BPay_803
  · exact WuPaper.ClassicalFourthNat.BPay_804
  · exact WuPaper.ClassicalFourthNat.BPay_805
  · exact WuPaper.ClassicalFourthNat.BPay_806
  · exact WuPaper.ClassicalFourthNat.BPay_807
  · exact WuPaper.ClassicalFourthNat.BPay_808
  · exact WuPaper.ClassicalFourthNat.BPay_809
  · exact WuPaper.ClassicalFourthNat.BPay_810
  · exact WuPaper.ClassicalFourthNat.BPay_811
  · exact WuPaper.ClassicalFourthNat.BPay_812
  · exact WuPaper.ClassicalFourthNat.BPay_813
  · exact WuPaper.ClassicalFourthNat.BPay_814
  · exact WuPaper.ClassicalFourthNat.BPay_815
  · exact WuPaper.ClassicalFourthNat.BPay_816
  · exact WuPaper.ClassicalFourthNat.BPay_817
  · exact WuPaper.ClassicalFourthNat.BPay_818
  · exact WuPaper.ClassicalFourthNat.BPay_819
  · exact WuPaper.ClassicalFourthNat.BPay_820
  · exact WuPaper.ClassicalFourthNat.BPay_821
  · exact WuPaper.ClassicalFourthNat.BPay_822
  · exact WuPaper.ClassicalFourthNat.BPay_823
  · exact WuPaper.ClassicalFourthNat.BPay_824
  · exact WuPaper.ClassicalFourthNat.BPay_825
  · exact WuPaper.ClassicalFourthNat.BPay_826
  · exact WuPaper.ClassicalFourthNat.BPay_827
  · exact WuPaper.ClassicalFourthNat.BPay_828
  · exact WuPaper.ClassicalFourthNat.BPay_829
  · exact WuPaper.ClassicalFourthNat.BPay_830
  · exact WuPaper.ClassicalFourthNat.BPay_831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_012

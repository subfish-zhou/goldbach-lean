import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay106
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_106 (j : Fin 64) (hj : 64*106+j.val < 10540) :
    OuterPay (64*106+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6784
  · exact WuPaper.ClassicalFourthNat.outerPay_6785
  · exact WuPaper.ClassicalFourthNat.outerPay_6786
  · exact WuPaper.ClassicalFourthNat.outerPay_6787
  · exact WuPaper.ClassicalFourthNat.outerPay_6788
  · exact WuPaper.ClassicalFourthNat.outerPay_6789
  · exact WuPaper.ClassicalFourthNat.outerPay_6790
  · exact WuPaper.ClassicalFourthNat.outerPay_6791
  · exact WuPaper.ClassicalFourthNat.outerPay_6792
  · exact WuPaper.ClassicalFourthNat.outerPay_6793
  · exact WuPaper.ClassicalFourthNat.outerPay_6794
  · exact WuPaper.ClassicalFourthNat.outerPay_6795
  · exact WuPaper.ClassicalFourthNat.outerPay_6796
  · exact WuPaper.ClassicalFourthNat.outerPay_6797
  · exact WuPaper.ClassicalFourthNat.outerPay_6798
  · exact WuPaper.ClassicalFourthNat.outerPay_6799
  · exact WuPaper.ClassicalFourthNat.outerPay_6800
  · exact WuPaper.ClassicalFourthNat.outerPay_6801
  · exact WuPaper.ClassicalFourthNat.outerPay_6802
  · exact WuPaper.ClassicalFourthNat.outerPay_6803
  · exact WuPaper.ClassicalFourthNat.outerPay_6804
  · exact WuPaper.ClassicalFourthNat.outerPay_6805
  · exact WuPaper.ClassicalFourthNat.outerPay_6806
  · exact WuPaper.ClassicalFourthNat.outerPay_6807
  · exact WuPaper.ClassicalFourthNat.outerPay_6808
  · exact WuPaper.ClassicalFourthNat.outerPay_6809
  · exact WuPaper.ClassicalFourthNat.outerPay_6810
  · exact WuPaper.ClassicalFourthNat.outerPay_6811
  · exact WuPaper.ClassicalFourthNat.outerPay_6812
  · exact WuPaper.ClassicalFourthNat.outerPay_6813
  · exact WuPaper.ClassicalFourthNat.outerPay_6814
  · exact WuPaper.ClassicalFourthNat.outerPay_6815
  · exact WuPaper.ClassicalFourthNat.outerPay_6816
  · exact WuPaper.ClassicalFourthNat.outerPay_6817
  · exact WuPaper.ClassicalFourthNat.outerPay_6818
  · exact WuPaper.ClassicalFourthNat.outerPay_6819
  · exact WuPaper.ClassicalFourthNat.outerPay_6820
  · exact WuPaper.ClassicalFourthNat.outerPay_6821
  · exact WuPaper.ClassicalFourthNat.outerPay_6822
  · exact WuPaper.ClassicalFourthNat.outerPay_6823
  · exact WuPaper.ClassicalFourthNat.outerPay_6824
  · exact WuPaper.ClassicalFourthNat.outerPay_6825
  · exact WuPaper.ClassicalFourthNat.outerPay_6826
  · exact WuPaper.ClassicalFourthNat.outerPay_6827
  · exact WuPaper.ClassicalFourthNat.outerPay_6828
  · exact WuPaper.ClassicalFourthNat.outerPay_6829
  · exact WuPaper.ClassicalFourthNat.outerPay_6830
  · exact WuPaper.ClassicalFourthNat.outerPay_6831
  · exact WuPaper.ClassicalFourthNat.outerPay_6832
  · exact WuPaper.ClassicalFourthNat.outerPay_6833
  · exact WuPaper.ClassicalFourthNat.outerPay_6834
  · exact WuPaper.ClassicalFourthNat.outerPay_6835
  · exact WuPaper.ClassicalFourthNat.outerPay_6836
  · exact WuPaper.ClassicalFourthNat.outerPay_6837
  · exact WuPaper.ClassicalFourthNat.outerPay_6838
  · exact WuPaper.ClassicalFourthNat.outerPay_6839
  · exact WuPaper.ClassicalFourthNat.outerPay_6840
  · exact WuPaper.ClassicalFourthNat.outerPay_6841
  · exact WuPaper.ClassicalFourthNat.outerPay_6842
  · exact WuPaper.ClassicalFourthNat.outerPay_6843
  · exact WuPaper.ClassicalFourthNat.outerPay_6844
  · exact WuPaper.ClassicalFourthNat.outerPay_6845
  · exact WuPaper.ClassicalFourthNat.outerPay_6846
  · exact WuPaper.ClassicalFourthNat.outerPay_6847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_106

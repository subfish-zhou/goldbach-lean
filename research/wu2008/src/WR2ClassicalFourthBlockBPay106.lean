import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay106
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_106 (j : Fin 64) (hj : 64*106+j.val < 10540) :
    BPay (64*106+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6784
  · exact WuPaper.ClassicalFourthNat.BPay_6785
  · exact WuPaper.ClassicalFourthNat.BPay_6786
  · exact WuPaper.ClassicalFourthNat.BPay_6787
  · exact WuPaper.ClassicalFourthNat.BPay_6788
  · exact WuPaper.ClassicalFourthNat.BPay_6789
  · exact WuPaper.ClassicalFourthNat.BPay_6790
  · exact WuPaper.ClassicalFourthNat.BPay_6791
  · exact WuPaper.ClassicalFourthNat.BPay_6792
  · exact WuPaper.ClassicalFourthNat.BPay_6793
  · exact WuPaper.ClassicalFourthNat.BPay_6794
  · exact WuPaper.ClassicalFourthNat.BPay_6795
  · exact WuPaper.ClassicalFourthNat.BPay_6796
  · exact WuPaper.ClassicalFourthNat.BPay_6797
  · exact WuPaper.ClassicalFourthNat.BPay_6798
  · exact WuPaper.ClassicalFourthNat.BPay_6799
  · exact WuPaper.ClassicalFourthNat.BPay_6800
  · exact WuPaper.ClassicalFourthNat.BPay_6801
  · exact WuPaper.ClassicalFourthNat.BPay_6802
  · exact WuPaper.ClassicalFourthNat.BPay_6803
  · exact WuPaper.ClassicalFourthNat.BPay_6804
  · exact WuPaper.ClassicalFourthNat.BPay_6805
  · exact WuPaper.ClassicalFourthNat.BPay_6806
  · exact WuPaper.ClassicalFourthNat.BPay_6807
  · exact WuPaper.ClassicalFourthNat.BPay_6808
  · exact WuPaper.ClassicalFourthNat.BPay_6809
  · exact WuPaper.ClassicalFourthNat.BPay_6810
  · exact WuPaper.ClassicalFourthNat.BPay_6811
  · exact WuPaper.ClassicalFourthNat.BPay_6812
  · exact WuPaper.ClassicalFourthNat.BPay_6813
  · exact WuPaper.ClassicalFourthNat.BPay_6814
  · exact WuPaper.ClassicalFourthNat.BPay_6815
  · exact WuPaper.ClassicalFourthNat.BPay_6816
  · exact WuPaper.ClassicalFourthNat.BPay_6817
  · exact WuPaper.ClassicalFourthNat.BPay_6818
  · exact WuPaper.ClassicalFourthNat.BPay_6819
  · exact WuPaper.ClassicalFourthNat.BPay_6820
  · exact WuPaper.ClassicalFourthNat.BPay_6821
  · exact WuPaper.ClassicalFourthNat.BPay_6822
  · exact WuPaper.ClassicalFourthNat.BPay_6823
  · exact WuPaper.ClassicalFourthNat.BPay_6824
  · exact WuPaper.ClassicalFourthNat.BPay_6825
  · exact WuPaper.ClassicalFourthNat.BPay_6826
  · exact WuPaper.ClassicalFourthNat.BPay_6827
  · exact WuPaper.ClassicalFourthNat.BPay_6828
  · exact WuPaper.ClassicalFourthNat.BPay_6829
  · exact WuPaper.ClassicalFourthNat.BPay_6830
  · exact WuPaper.ClassicalFourthNat.BPay_6831
  · exact WuPaper.ClassicalFourthNat.BPay_6832
  · exact WuPaper.ClassicalFourthNat.BPay_6833
  · exact WuPaper.ClassicalFourthNat.BPay_6834
  · exact WuPaper.ClassicalFourthNat.BPay_6835
  · exact WuPaper.ClassicalFourthNat.BPay_6836
  · exact WuPaper.ClassicalFourthNat.BPay_6837
  · exact WuPaper.ClassicalFourthNat.BPay_6838
  · exact WuPaper.ClassicalFourthNat.BPay_6839
  · exact WuPaper.ClassicalFourthNat.BPay_6840
  · exact WuPaper.ClassicalFourthNat.BPay_6841
  · exact WuPaper.ClassicalFourthNat.BPay_6842
  · exact WuPaper.ClassicalFourthNat.BPay_6843
  · exact WuPaper.ClassicalFourthNat.BPay_6844
  · exact WuPaper.ClassicalFourthNat.BPay_6845
  · exact WuPaper.ClassicalFourthNat.BPay_6846
  · exact WuPaper.ClassicalFourthNat.BPay_6847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_106

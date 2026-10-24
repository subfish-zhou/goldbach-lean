import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay137
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_137 (j : Fin 64) (hj : 64*137+j.val < 10540) :
    BPay (64*137+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8768
  · exact WuPaper.ClassicalFourthNat.BPay_8769
  · exact WuPaper.ClassicalFourthNat.BPay_8770
  · exact WuPaper.ClassicalFourthNat.BPay_8771
  · exact WuPaper.ClassicalFourthNat.BPay_8772
  · exact WuPaper.ClassicalFourthNat.BPay_8773
  · exact WuPaper.ClassicalFourthNat.BPay_8774
  · exact WuPaper.ClassicalFourthNat.BPay_8775
  · exact WuPaper.ClassicalFourthNat.BPay_8776
  · exact WuPaper.ClassicalFourthNat.BPay_8777
  · exact WuPaper.ClassicalFourthNat.BPay_8778
  · exact WuPaper.ClassicalFourthNat.BPay_8779
  · exact WuPaper.ClassicalFourthNat.BPay_8780
  · exact WuPaper.ClassicalFourthNat.BPay_8781
  · exact WuPaper.ClassicalFourthNat.BPay_8782
  · exact WuPaper.ClassicalFourthNat.BPay_8783
  · exact WuPaper.ClassicalFourthNat.BPay_8784
  · exact WuPaper.ClassicalFourthNat.BPay_8785
  · exact WuPaper.ClassicalFourthNat.BPay_8786
  · exact WuPaper.ClassicalFourthNat.BPay_8787
  · exact WuPaper.ClassicalFourthNat.BPay_8788
  · exact WuPaper.ClassicalFourthNat.BPay_8789
  · exact WuPaper.ClassicalFourthNat.BPay_8790
  · exact WuPaper.ClassicalFourthNat.BPay_8791
  · exact WuPaper.ClassicalFourthNat.BPay_8792
  · exact WuPaper.ClassicalFourthNat.BPay_8793
  · exact WuPaper.ClassicalFourthNat.BPay_8794
  · exact WuPaper.ClassicalFourthNat.BPay_8795
  · exact WuPaper.ClassicalFourthNat.BPay_8796
  · exact WuPaper.ClassicalFourthNat.BPay_8797
  · exact WuPaper.ClassicalFourthNat.BPay_8798
  · exact WuPaper.ClassicalFourthNat.BPay_8799
  · exact WuPaper.ClassicalFourthNat.BPay_8800
  · exact WuPaper.ClassicalFourthNat.BPay_8801
  · exact WuPaper.ClassicalFourthNat.BPay_8802
  · exact WuPaper.ClassicalFourthNat.BPay_8803
  · exact WuPaper.ClassicalFourthNat.BPay_8804
  · exact WuPaper.ClassicalFourthNat.BPay_8805
  · exact WuPaper.ClassicalFourthNat.BPay_8806
  · exact WuPaper.ClassicalFourthNat.BPay_8807
  · exact WuPaper.ClassicalFourthNat.BPay_8808
  · exact WuPaper.ClassicalFourthNat.BPay_8809
  · exact WuPaper.ClassicalFourthNat.BPay_8810
  · exact WuPaper.ClassicalFourthNat.BPay_8811
  · exact WuPaper.ClassicalFourthNat.BPay_8812
  · exact WuPaper.ClassicalFourthNat.BPay_8813
  · exact WuPaper.ClassicalFourthNat.BPay_8814
  · exact WuPaper.ClassicalFourthNat.BPay_8815
  · exact WuPaper.ClassicalFourthNat.BPay_8816
  · exact WuPaper.ClassicalFourthNat.BPay_8817
  · exact WuPaper.ClassicalFourthNat.BPay_8818
  · exact WuPaper.ClassicalFourthNat.BPay_8819
  · exact WuPaper.ClassicalFourthNat.BPay_8820
  · exact WuPaper.ClassicalFourthNat.BPay_8821
  · exact WuPaper.ClassicalFourthNat.BPay_8822
  · exact WuPaper.ClassicalFourthNat.BPay_8823
  · exact WuPaper.ClassicalFourthNat.BPay_8824
  · exact WuPaper.ClassicalFourthNat.BPay_8825
  · exact WuPaper.ClassicalFourthNat.BPay_8826
  · exact WuPaper.ClassicalFourthNat.BPay_8827
  · exact WuPaper.ClassicalFourthNat.BPay_8828
  · exact WuPaper.ClassicalFourthNat.BPay_8829
  · exact WuPaper.ClassicalFourthNat.BPay_8830
  · exact WuPaper.ClassicalFourthNat.BPay_8831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_137

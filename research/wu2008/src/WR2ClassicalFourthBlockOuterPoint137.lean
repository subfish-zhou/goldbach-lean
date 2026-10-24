import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint137
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_137 (j : Fin 64) (hj : 64*137+j.val < 10541) :
    OuterPoint (64*137+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8768
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8769
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8770
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8771
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8772
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8773
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8774
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8775
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8776
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8777
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8778
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8779
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8780
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8781
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8782
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8783
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8784
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8785
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8786
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8787
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8788
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8789
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8790
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8791
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8792
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8793
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8794
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8795
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8796
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8797
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8798
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8799
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8800
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8801
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8802
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8803
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8804
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8805
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8806
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8807
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8808
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8809
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8810
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8811
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8812
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8813
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8814
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8815
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8816
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8817
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8818
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8819
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8820
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8821
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8822
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8823
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8824
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8825
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8826
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8827
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8828
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8829
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8830
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_137
